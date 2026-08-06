import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage001Count : Nat := 3

def config164Stage001Length : Nat := 5

set_option maxRecDepth 100000 in
def config164Stage001Tree : NatTree :=
  NatTree.node 1 (NatTree.leaf 189) (NatTree.node 1 (NatTree.leaf 193) (NatTree.leaf 197))

def config164Stage001Source : SourceTable := config164Stage001Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
