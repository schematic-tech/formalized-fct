import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage011Count : Nat := 60

def config164Stage011Length : Nat := 9

set_option maxRecDepth 100000 in
def config164Stage011Tree : NatTree :=
  NatTree.node 30 (NatTree.node 15 (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 735) (NatTree.node 1 (NatTree.leaf 9483) (NatTree.leaf 12399))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 15801) (NatTree.leaf 11427)) (NatTree.node 1 (NatTree.leaf 5595) (NatTree.leaf 4137)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 771) (NatTree.leaf 9519)) (NatTree.node 1 (NatTree.leaf 12435) (NatTree.leaf 15837))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 11463) (NatTree.leaf 5631)) (NatTree.node 1 (NatTree.leaf 4173) (NatTree.leaf 807))))) (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 9555) (NatTree.node 1 (NatTree.leaf 12471) (NatTree.leaf 15873))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 11499) (NatTree.leaf 5667)) (NatTree.node 1 (NatTree.leaf 4209) (NatTree.leaf 7)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 8755) (NatTree.leaf 5839)) (NatTree.node 1 (NatTree.leaf 13615) (NatTree.leaf 10699))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 19447) (NatTree.leaf 43)) (NatTree.node 1 (NatTree.leaf 8791) (NatTree.leaf 5875)))))) (NatTree.node 15 (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 13651) (NatTree.node 1 (NatTree.leaf 10735) (NatTree.leaf 19483))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 79) (NatTree.leaf 8827)) (NatTree.node 1 (NatTree.leaf 5911) (NatTree.leaf 13687)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 10771) (NatTree.leaf 19519)) (NatTree.node 1 (NatTree.leaf 15317) (NatTree.leaf 13859))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 8027) (NatTree.leaf 3653)) (NatTree.node 1 (NatTree.leaf 7055) (NatTree.leaf 9971))))) (NatTree.node 7 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 18719) (NatTree.node 1 (NatTree.leaf 15353) (NatTree.leaf 13895))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 8063) (NatTree.leaf 3689)) (NatTree.node 1 (NatTree.leaf 7091) (NatTree.leaf 10007)))) (NatTree.node 4 (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 18755) (NatTree.leaf 15389)) (NatTree.node 1 (NatTree.leaf 13931) (NatTree.leaf 8099))) (NatTree.node 2 (NatTree.node 1 (NatTree.leaf 3725) (NatTree.leaf 7127)) (NatTree.node 1 (NatTree.leaf 10043) (NatTree.leaf 18791))))))

def config164Stage011Source : SourceTable := config164Stage011Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
