import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage007Count : Nat := 24

def config164Stage007Length : Nat := 8

set_option maxRecDepth 100000 in
def config164Stage007Tree : NatTree :=
  NatTree.node 12 (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 3666) (NatTree.node 1 (NatTree.leaf 3774) (NatTree.leaf 3882))) (NatTree.node 1 (NatTree.leaf 24) (NatTree.node 1 (NatTree.leaf 5856) (NatTree.leaf 132)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 5964) (NatTree.node 1 (NatTree.leaf 240) (NatTree.leaf 6072))) (NatTree.node 1 (NatTree.leaf 3664) (NatTree.node 1 (NatTree.leaf 3772) (NatTree.leaf 3880))))) (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 2212) (NatTree.node 1 (NatTree.leaf 2320) (NatTree.leaf 2428))) (NatTree.node 1 (NatTree.leaf 20) (NatTree.node 1 (NatTree.leaf 5852) (NatTree.leaf 128)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 5960) (NatTree.node 1 (NatTree.leaf 236) (NatTree.leaf 6068))) (NatTree.node 1 (NatTree.leaf 2210) (NatTree.node 1 (NatTree.leaf 2318) (NatTree.leaf 2426)))))

def config164Stage007Source : SourceTable := config164Stage007Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
