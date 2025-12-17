/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump("ConstraintGraph");

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void Andersen::runPointerAnalysis()
{
    // 定义工作列表 (WorkList)，用于存储需要处理的节点 ID
    WorkList<unsigned> nodeQueue;

    // =========================================================
    // 第一阶段：初始化指向集 (处理取地址约束)
    // =========================================================
    // 遍历约束图中的所有节点，寻找 "p = &x" 形式的初始约束
    for (const auto& nodePair : *consg)
    {
        auto nodeID = nodePair.first;
        auto* constraintNode = nodePair.second;

        // 处理入边的 Address Edge
        for (auto* edge : constraintNode->getAddrInEdges())
        {
            if (auto* addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge))
            {
                auto srcVar = addrEdge->getSrcID(); // 被取地址的变量 (x)
                auto dstPtr = addrEdge->getDstID(); // 指针变量 (p)

                // 将 x 加入到 p 的指向集 pts(p) 中
                // 如果集合发生了变化（插入成功），则将 p 加入工作列表
                if (pts[dstPtr].insert(srcVar).second) {
                    nodeQueue.push(dstPtr);
                }
            }
        }
    }

    // 辅助 Lambda 函数：检查两个节点之间是否已经存在 Copy 边
    // 用于防止重复添加相同的边，避免图变得无限大或浪费计算资源
    auto copyEdgeExists = [&](unsigned src, unsigned dst) -> bool {
        auto* srcNode = consg->getConstraintNode(src);
        for (auto* outEdge : srcNode->getCopyOutEdges()) {
            if (outEdge->getDstID() == dst) return true;
        }
        return false;
    };

    // =========================================================
    // 第二阶段：计算传递闭包 (Worklist 算法主循环)
    // =========================================================
    while (!nodeQueue.empty())
    {
        // 从队列中取出一个节点作为当前处理节点
        auto currID = nodeQueue.pop();
        auto* currNode = consg->getConstraintNode(currID);
        const auto& currentObjects = pts[currID]; // 获取当前节点的指向集引用

        // -----------------------------------------------------
        // 部分 A: 处理复杂约束 (Store 和 Load)
        // 核心思想：遍历当前指针指向的所有对象 obj
        // -----------------------------------------------------
        for (auto obj : currentObjects)
        {
            // 情况 1: 处理 Store 指令 (*currID = val)
            // 语义：将 val 的值存入 currID 指向的对象 obj 中
            // 动作：添加一条 Copy 边 (val -> obj)
            for (auto* edge : currNode->getStoreInEdges())
            {
                if (auto* storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge))
                {
                    auto val = storeEdge->getSrcID();
                    // 如果边不存在，则添加并激活源节点
                    if (!copyEdgeExists(val, obj)) {
                        consg->addCopyCGEdge(val, obj);
                        nodeQueue.push(val); // 重新处理 val，使其指向集流向 obj
                    }
                }
            }

            // 情况 2: 处理 Load 指令 (val = *currID)
            // 语义：从 currID 指向的对象 obj 中读取值赋给 val
            // 动作：添加一条 Copy 边 (obj -> val)
            for (auto* edge : currNode->getLoadOutEdges())
            {
                if (auto* loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge))
                {
                    auto val = loadEdge->getDstID();
                    // 如果边不存在，则添加并激活源节点
                    if (!copyEdgeExists(obj, val)) {
                        consg->addCopyCGEdge(obj, val);
                        nodeQueue.push(obj); // 重新处理 obj，使其指向集流向 val
                    }
                }
            }
        }

        // -----------------------------------------------------
        // 部分 B: 处理 Copy 约束 (指针赋值传播)
        // 语义：currID = y  =>  pts(currID) ⊆ pts(y) (此处方向取决于边的方向)
        // 如果当前节点有一条 Copy 边指向 dstID (currID -> dstID)
        // -----------------------------------------------------
        for (auto* edge : currNode->getCopyOutEdges())
        {
            if (auto* copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge))
            {
                auto dstID = copyEdge->getDstID();
                size_t oldSize = pts[dstID].size();
                
                // 集合并集操作：pts(dst) U= pts(curr)
                pts[dstID].insert(currentObjects.begin(), currentObjects.end());

                // 如果目标节点的指向集变大了，说明信息更新了，加入队列继续处理
                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }

        // -----------------------------------------------------
        // 部分 C: 处理 GEP 约束 (结构体/数组字段访问)
        // 语义：currID --GEP--> dst
        // -----------------------------------------------------
        for (auto* edge : currNode->getGepOutEdges())
        {
            if (auto* gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge))
            {
                auto dstID = gepEdge->getDstID();
                size_t oldSize = pts[dstID].size();

                // 对于 currID 指向的每个对象 obj，计算其字段偏移后的新对象
                for (auto obj : currentObjects) {
                    auto fieldObj = consg->getGepObjVar(obj, gepEdge);
                    pts[dstID].insert(fieldObj);
                }

                // 如果目标节点的指向集变化，加入队列
                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }
    }
}
