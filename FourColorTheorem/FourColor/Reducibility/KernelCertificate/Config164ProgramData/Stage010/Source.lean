import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage010Count : Nat := 60

def config164Stage010Length : Nat := 9

set_option maxRecDepth 100000 in
def config164Stage010Tree : NatTree :=
  NatTree.node 30 (NatTree.node 15 (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 189) (NatTree.node 1 (NatTree.leaf 1161) (NatTree.leaf 2133))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 13347) (NatTree.leaf 14319)) (NatTree.node 1 (NatTree.leaf 15291) (NatTree.leaf 13329)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 14301) (NatTree.leaf 15273)) (NatTree.node 1 (NatTree.leaf 201) (NatTree.leaf 1173))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 2145) (NatTree.leaf 13305)) (NatTree.node 1 (NatTree.leaf 14277) (NatTree.leaf 15249))))) (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 237) (NatTree.node 1 (NatTree.leaf 1209) (NatTree.leaf 2181))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 13299) (NatTree.leaf 14271)) (NatTree.node 1 (NatTree.leaf 15243) (NatTree.leaf 163)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 1135) (NatTree.leaf 2107)) (NatTree.node 1 (NatTree.leaf 235) (NatTree.leaf 1207))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 2179) (NatTree.leaf 175)) (NatTree.node 1 (NatTree.leaf 1147) (NatTree.leaf 2119)))))) (NatTree.node 15 (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 13351) (NatTree.node 1 (NatTree.leaf 14323) (NatTree.leaf 15295))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 13291) (NatTree.leaf 14263)) (NatTree.node 1 (NatTree.leaf 15235) (NatTree.leaf 13363)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 14335) (NatTree.leaf 15307)) (NatTree.node 1 (NatTree.leaf 227) (NatTree.leaf 1199))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 2171) (NatTree.leaf 13289)) (NatTree.node 1 (NatTree.leaf 14261) (NatTree.leaf 15233))))) (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 221) (NatTree.node 1 (NatTree.leaf 1193) (NatTree.leaf 2165))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 13325) (NatTree.leaf 14297)) (NatTree.node 1 (NatTree.leaf 15269) (NatTree.leaf 197)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 1169) (NatTree.leaf 2141)) (NatTree.node 1 (NatTree.leaf 179) (NatTree.leaf 1151))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 2123) (NatTree.leaf 13337)) (NatTree.node 1 (NatTree.leaf 14309) (NatTree.leaf 15281))))))

def config164Stage010Source : SourceTable := config164Stage010Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
