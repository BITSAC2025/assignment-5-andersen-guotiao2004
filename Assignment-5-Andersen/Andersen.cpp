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
    // WorkList definition from A5Header.h
    WorkList<unsigned> nodeQueue;

    // =========================================================
    // Phase 1: Initialize Points-to Sets (Handling Address-of)
    // =========================================================
    for (const auto& nodePair : *consg)
    {
        auto nodeID = nodePair.first;
        auto* constraintNode = nodePair.second;

        // Process incoming Address edges: p = &x
        for (auto* edge : constraintNode->getAddrInEdges())
        {
            if (auto* addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge))
            {
                auto srcVar = addrEdge->getSrcID(); // The variable being taken address of
                auto dstPtr = addrEdge->getDstID(); // The pointer variable

                // Insert src into pts(dst)
                if (pts[dstPtr].insert(srcVar).second) {
                    nodeQueue.push(dstPtr);
                }
            }
        }
    }

    // Helper Lambda: Check if a Copy edge exists between two nodes to avoid duplicates
    auto copyEdgeExists = [&](unsigned src, unsigned dst) -> bool {
        auto* srcNode = consg->getConstraintNode(src);
        for (auto* outEdge : srcNode->getCopyOutEdges()) {
            if (outEdge->getDstID() == dst) return true;
        }
        return false;
    };

    // =========================================================
    // Phase 2: Transitive Closure (Worklist Algorithm)
    // =========================================================
    while (!nodeQueue.empty())
    {
        auto currID = nodeQueue.pop();
        auto* currNode = consg->getConstraintNode(currID);
        const auto& currentObjects = pts[currID]; // Current points-to set

        // -----------------------------------------------------
        // Part A: Handle Complex Constraints (Store & Load)
        // Iterate over all objects 'obj' that 'currID' points to
        // -----------------------------------------------------
        for (auto obj : currentObjects)
        {
            // Case 1: Store *currID = val
            // Constraint: val --Store--> currID
            // Action: Add edge val --Copy--> obj
            for (auto* edge : currNode->getStoreInEdges())
            {
                if (auto* storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge))
                {
                    auto val = storeEdge->getSrcID();
                    if (!copyEdgeExists(val, obj)) {
                        consg->addCopyCGEdge(val, obj);
                        nodeQueue.push(val); // Re-process source to propagate data
                    }
                }
            }

            // Case 2: Load val = *currID
            // Constraint: currID --Load--> val
            // Action: Add edge obj --Copy--> val
            for (auto* edge : currNode->getLoadOutEdges())
            {
                if (auto* loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge))
                {
                    auto val = loadEdge->getDstID();
                    if (!copyEdgeExists(obj, val)) {
                        consg->addCopyCGEdge(obj, val);
                        nodeQueue.push(obj); // Re-process object to propagate data
                    }
                }
            }
        }

        // -----------------------------------------------------
        // Part B: Handle Copy Constraints (Propagation)
        // currID = y  =>  pts(currID) ⊆ pts(y)
        // -----------------------------------------------------
        for (auto* edge : currNode->getCopyOutEdges())
        {
            if (auto* copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge))
            {
                auto dstID = copyEdge->getDstID();
                size_t oldSize = pts[dstID].size();
                
                // Union sets: pts(dst) U= pts(curr)
                pts[dstID].insert(currentObjects.begin(), currentObjects.end());

                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }

        // -----------------------------------------------------
        // Part C: Handle GEP Constraints (Field Access)
        // currID --GEP--> dst
        // -----------------------------------------------------
        for (auto* edge : currNode->getGepOutEdges())
        {
            if (auto* gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge))
            {
                auto dstID = gepEdge->getDstID();
                size_t oldSize = pts[dstID].size();

                for (auto obj : currentObjects) {
                    auto fieldObj = consg->getGepObjVar(obj, gepEdge);
                    pts[dstID].insert(fieldObj);
                }

                if (pts[dstID].size() > oldSize) {
                    nodeQueue.push(dstID);
                }
            }
        }
    }
}
