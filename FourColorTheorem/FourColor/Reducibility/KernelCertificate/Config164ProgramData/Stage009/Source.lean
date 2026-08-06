import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage009Count : Nat := 48

def config164Stage009Length : Nat := 9

set_option maxRecDepth 100000 in
def config164Stage009Tree : NatTree :=
  NatTree.node 24 (NatTree.node 12 (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 171) (NatTree.node 1 (NatTree.leaf 1143) (NatTree.leaf 2115))) (NatTree.node 1 (NatTree.leaf 165) (NatTree.node 1 (NatTree.leaf 1137) (NatTree.leaf 2109)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 237) (NatTree.node 1 (NatTree.leaf 1209) (NatTree.leaf 2181))) (NatTree.node 1 (NatTree.leaf 231) (NatTree.node 1 (NatTree.leaf 1203) (NatTree.leaf 2175))))) (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 199) (NatTree.node 1 (NatTree.leaf 1171) (NatTree.leaf 2143))) (NatTree.node 1 (NatTree.leaf 13303) (NatTree.node 1 (NatTree.leaf 14275) (NatTree.leaf 15247)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 235) (NatTree.node 1 (NatTree.leaf 1207) (NatTree.leaf 2179))) (NatTree.node 1 (NatTree.leaf 193) (NatTree.node 1 (NatTree.leaf 1165) (NatTree.leaf 2137)))))) (NatTree.node 12 (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 13333) (NatTree.node 1 (NatTree.leaf 14305) (NatTree.leaf 15277))) (NatTree.node 1 (NatTree.leaf 13291) (NatTree.node 1 (NatTree.leaf 14263) (NatTree.leaf 15235)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 223) (NatTree.node 1 (NatTree.leaf 1195) (NatTree.leaf 2167))) (NatTree.node 1 (NatTree.leaf 13327) (NatTree.node 1 (NatTree.leaf 14299) (NatTree.leaf 15271))))) (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 13295) (NatTree.node 1 (NatTree.leaf 14267) (NatTree.leaf 15239))) (NatTree.node 1 (NatTree.leaf 13289) (NatTree.node 1 (NatTree.leaf 14261) (NatTree.leaf 15233)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 13361) (NatTree.node 1 (NatTree.leaf 14333) (NatTree.leaf 15305))) (NatTree.node 1 (NatTree.leaf 13355) (NatTree.node 1 (NatTree.leaf 14327) (NatTree.leaf 15299))))))

def config164Stage009Source : SourceTable := config164Stage009Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
