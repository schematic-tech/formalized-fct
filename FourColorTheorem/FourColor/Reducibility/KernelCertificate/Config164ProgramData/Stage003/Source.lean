import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage003Count : Nat := 6

def config164Stage003Length : Nat := 6

set_option maxRecDepth 100000 in
def config164Stage003Tree : NatTree :=
  NatTree.node 3 (NatTree.node 1 (NatTree.leaf 24) (NatTree.node 1 (NatTree.leaf 132) (NatTree.leaf 240))) (NatTree.node 1 (NatTree.leaf 20) (NatTree.node 1 (NatTree.leaf 128) (NatTree.leaf 236)))

def config164Stage003Source : SourceTable := config164Stage003Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
