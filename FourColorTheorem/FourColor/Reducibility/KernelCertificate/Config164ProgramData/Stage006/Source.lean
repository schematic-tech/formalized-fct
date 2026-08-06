import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage006Count : Nat := 12

def config164Stage006Length : Nat := 7

set_option maxRecDepth 100000 in
def config164Stage006Tree : NatTree :=
  NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 735) (NatTree.node 1 (NatTree.leaf 771) (NatTree.leaf 807))) (NatTree.node 1 (NatTree.leaf 7) (NatTree.node 1 (NatTree.leaf 1951) (NatTree.leaf 43)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 1987) (NatTree.node 1 (NatTree.leaf 79) (NatTree.leaf 2023))) (NatTree.node 1 (NatTree.leaf 1223) (NatTree.node 1 (NatTree.leaf 1259) (NatTree.leaf 1295))))

def config164Stage006Source : SourceTable := config164Stage006Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
