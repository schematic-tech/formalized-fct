import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage000Count : Nat := 1

def config164Stage000Length : Nat := 3

set_option maxRecDepth 100000 in
def config164Stage000Tree : NatTree :=
  NatTree.leaf 21

def config164Stage000Source : SourceTable := config164Stage000Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
