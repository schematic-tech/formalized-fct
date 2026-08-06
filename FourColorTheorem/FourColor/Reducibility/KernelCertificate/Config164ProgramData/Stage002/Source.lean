import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage002Count : Nat := 3

def config164Stage002Length : Nat := 5

set_option maxRecDepth 100000 in
def config164Stage002Tree : NatTree :=
  NatTree.node 1 (NatTree.leaf 7) (NatTree.node 1 (NatTree.leaf 43) (NatTree.leaf 79))

def config164Stage002Source : SourceTable := config164Stage002Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
