import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage004Count : Nat := 6

def config164Stage004Length : Nat := 6

set_option maxRecDepth 100000 in
def config164Stage004Tree : NatTree :=
  NatTree.node 3 (NatTree.node 1 (NatTree.leaf 492) (NatTree.node 1 (NatTree.leaf 528) (NatTree.leaf 564))) (NatTree.node 1 (NatTree.leaf 8) (NatTree.node 1 (NatTree.leaf 44) (NatTree.leaf 80)))

def config164Stage004Source : SourceTable := config164Stage004Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
