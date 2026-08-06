import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks000
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks001
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks002
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks003
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks004
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks005
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks006
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks007
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks008
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks009
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks010
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks011
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks012
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks013
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks014
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks015
import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data.SourceBlocks016

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164BaseCount : Nat := 24315

def config164SourceCount : Nat := 67325

def config164SourceGroup000 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0000 index
  | 1 => NatTree.get config164SourceBlock0001 (index - 256)
  | 2 => NatTree.get config164SourceBlock0002 (index - 512)
  | 3 => NatTree.get config164SourceBlock0003 (index - 768)
  | 4 => NatTree.get config164SourceBlock0004 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0005 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0006 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0007 (index - 1792)
  | _ => none

def config164SourceGroup001 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0008 index
  | 1 => NatTree.get config164SourceBlock0009 (index - 256)
  | 2 => NatTree.get config164SourceBlock0010 (index - 512)
  | 3 => NatTree.get config164SourceBlock0011 (index - 768)
  | 4 => NatTree.get config164SourceBlock0012 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0013 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0014 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0015 (index - 1792)
  | _ => none

def config164SourceGroup002 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0016 index
  | 1 => NatTree.get config164SourceBlock0017 (index - 256)
  | 2 => NatTree.get config164SourceBlock0018 (index - 512)
  | 3 => NatTree.get config164SourceBlock0019 (index - 768)
  | 4 => NatTree.get config164SourceBlock0020 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0021 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0022 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0023 (index - 1792)
  | _ => none

def config164SourceGroup003 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0024 index
  | 1 => NatTree.get config164SourceBlock0025 (index - 256)
  | 2 => NatTree.get config164SourceBlock0026 (index - 512)
  | 3 => NatTree.get config164SourceBlock0027 (index - 768)
  | 4 => NatTree.get config164SourceBlock0028 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0029 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0030 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0031 (index - 1792)
  | _ => none

def config164SourceGroup004 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0032 index
  | 1 => NatTree.get config164SourceBlock0033 (index - 256)
  | 2 => NatTree.get config164SourceBlock0034 (index - 512)
  | 3 => NatTree.get config164SourceBlock0035 (index - 768)
  | 4 => NatTree.get config164SourceBlock0036 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0037 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0038 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0039 (index - 1792)
  | _ => none

def config164SourceGroup005 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0040 index
  | 1 => NatTree.get config164SourceBlock0041 (index - 256)
  | 2 => NatTree.get config164SourceBlock0042 (index - 512)
  | 3 => NatTree.get config164SourceBlock0043 (index - 768)
  | 4 => NatTree.get config164SourceBlock0044 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0045 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0046 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0047 (index - 1792)
  | _ => none

def config164SourceGroup006 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0048 index
  | 1 => NatTree.get config164SourceBlock0049 (index - 256)
  | 2 => NatTree.get config164SourceBlock0050 (index - 512)
  | 3 => NatTree.get config164SourceBlock0051 (index - 768)
  | 4 => NatTree.get config164SourceBlock0052 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0053 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0054 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0055 (index - 1792)
  | _ => none

def config164SourceGroup007 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0056 index
  | 1 => NatTree.get config164SourceBlock0057 (index - 256)
  | 2 => NatTree.get config164SourceBlock0058 (index - 512)
  | 3 => NatTree.get config164SourceBlock0059 (index - 768)
  | 4 => NatTree.get config164SourceBlock0060 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0061 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0062 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0063 (index - 1792)
  | _ => none

def config164SourceGroup008 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0064 index
  | 1 => NatTree.get config164SourceBlock0065 (index - 256)
  | 2 => NatTree.get config164SourceBlock0066 (index - 512)
  | 3 => NatTree.get config164SourceBlock0067 (index - 768)
  | 4 => NatTree.get config164SourceBlock0068 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0069 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0070 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0071 (index - 1792)
  | _ => none

def config164SourceGroup009 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0072 index
  | 1 => NatTree.get config164SourceBlock0073 (index - 256)
  | 2 => NatTree.get config164SourceBlock0074 (index - 512)
  | 3 => NatTree.get config164SourceBlock0075 (index - 768)
  | 4 => NatTree.get config164SourceBlock0076 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0077 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0078 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0079 (index - 1792)
  | _ => none

def config164SourceGroup010 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0080 index
  | 1 => NatTree.get config164SourceBlock0081 (index - 256)
  | 2 => NatTree.get config164SourceBlock0082 (index - 512)
  | 3 => NatTree.get config164SourceBlock0083 (index - 768)
  | 4 => NatTree.get config164SourceBlock0084 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0085 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0086 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0087 (index - 1792)
  | _ => none

def config164SourceGroup011 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0088 index
  | 1 => NatTree.get config164SourceBlock0089 (index - 256)
  | 2 => NatTree.get config164SourceBlock0090 (index - 512)
  | 3 => NatTree.get config164SourceBlock0091 (index - 768)
  | 4 => NatTree.get config164SourceBlock0092 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0093 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0094 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0095 (index - 1792)
  | _ => none

def config164SourceGroup012 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0096 index
  | 1 => NatTree.get config164SourceBlock0097 (index - 256)
  | 2 => NatTree.get config164SourceBlock0098 (index - 512)
  | 3 => NatTree.get config164SourceBlock0099 (index - 768)
  | 4 => NatTree.get config164SourceBlock0100 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0101 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0102 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0103 (index - 1792)
  | _ => none

def config164SourceGroup013 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0104 index
  | 1 => NatTree.get config164SourceBlock0105 (index - 256)
  | 2 => NatTree.get config164SourceBlock0106 (index - 512)
  | 3 => NatTree.get config164SourceBlock0107 (index - 768)
  | 4 => NatTree.get config164SourceBlock0108 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0109 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0110 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0111 (index - 1792)
  | _ => none

def config164SourceGroup014 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0112 index
  | 1 => NatTree.get config164SourceBlock0113 (index - 256)
  | 2 => NatTree.get config164SourceBlock0114 (index - 512)
  | 3 => NatTree.get config164SourceBlock0115 (index - 768)
  | 4 => NatTree.get config164SourceBlock0116 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0117 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0118 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0119 (index - 1792)
  | _ => none

def config164SourceGroup015 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0120 index
  | 1 => NatTree.get config164SourceBlock0121 (index - 256)
  | 2 => NatTree.get config164SourceBlock0122 (index - 512)
  | 3 => NatTree.get config164SourceBlock0123 (index - 768)
  | 4 => NatTree.get config164SourceBlock0124 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0125 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0126 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0127 (index - 1792)
  | _ => none

def config164SourceGroup016 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0128 index
  | 1 => NatTree.get config164SourceBlock0129 (index - 256)
  | 2 => NatTree.get config164SourceBlock0130 (index - 512)
  | 3 => NatTree.get config164SourceBlock0131 (index - 768)
  | 4 => NatTree.get config164SourceBlock0132 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0133 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0134 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0135 (index - 1792)
  | _ => none

def config164SourceGroup017 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0136 index
  | 1 => NatTree.get config164SourceBlock0137 (index - 256)
  | 2 => NatTree.get config164SourceBlock0138 (index - 512)
  | 3 => NatTree.get config164SourceBlock0139 (index - 768)
  | 4 => NatTree.get config164SourceBlock0140 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0141 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0142 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0143 (index - 1792)
  | _ => none

def config164SourceGroup018 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0144 index
  | 1 => NatTree.get config164SourceBlock0145 (index - 256)
  | 2 => NatTree.get config164SourceBlock0146 (index - 512)
  | 3 => NatTree.get config164SourceBlock0147 (index - 768)
  | 4 => NatTree.get config164SourceBlock0148 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0149 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0150 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0151 (index - 1792)
  | _ => none

def config164SourceGroup019 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0152 index
  | 1 => NatTree.get config164SourceBlock0153 (index - 256)
  | 2 => NatTree.get config164SourceBlock0154 (index - 512)
  | 3 => NatTree.get config164SourceBlock0155 (index - 768)
  | 4 => NatTree.get config164SourceBlock0156 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0157 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0158 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0159 (index - 1792)
  | _ => none

def config164SourceGroup020 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0160 index
  | 1 => NatTree.get config164SourceBlock0161 (index - 256)
  | 2 => NatTree.get config164SourceBlock0162 (index - 512)
  | 3 => NatTree.get config164SourceBlock0163 (index - 768)
  | 4 => NatTree.get config164SourceBlock0164 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0165 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0166 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0167 (index - 1792)
  | _ => none

def config164SourceGroup021 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0168 index
  | 1 => NatTree.get config164SourceBlock0169 (index - 256)
  | 2 => NatTree.get config164SourceBlock0170 (index - 512)
  | 3 => NatTree.get config164SourceBlock0171 (index - 768)
  | 4 => NatTree.get config164SourceBlock0172 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0173 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0174 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0175 (index - 1792)
  | _ => none

def config164SourceGroup022 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0176 index
  | 1 => NatTree.get config164SourceBlock0177 (index - 256)
  | 2 => NatTree.get config164SourceBlock0178 (index - 512)
  | 3 => NatTree.get config164SourceBlock0179 (index - 768)
  | 4 => NatTree.get config164SourceBlock0180 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0181 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0182 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0183 (index - 1792)
  | _ => none

def config164SourceGroup023 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0184 index
  | 1 => NatTree.get config164SourceBlock0185 (index - 256)
  | 2 => NatTree.get config164SourceBlock0186 (index - 512)
  | 3 => NatTree.get config164SourceBlock0187 (index - 768)
  | 4 => NatTree.get config164SourceBlock0188 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0189 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0190 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0191 (index - 1792)
  | _ => none

def config164SourceGroup024 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0192 index
  | 1 => NatTree.get config164SourceBlock0193 (index - 256)
  | 2 => NatTree.get config164SourceBlock0194 (index - 512)
  | 3 => NatTree.get config164SourceBlock0195 (index - 768)
  | 4 => NatTree.get config164SourceBlock0196 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0197 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0198 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0199 (index - 1792)
  | _ => none

def config164SourceGroup025 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0200 index
  | 1 => NatTree.get config164SourceBlock0201 (index - 256)
  | 2 => NatTree.get config164SourceBlock0202 (index - 512)
  | 3 => NatTree.get config164SourceBlock0203 (index - 768)
  | 4 => NatTree.get config164SourceBlock0204 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0205 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0206 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0207 (index - 1792)
  | _ => none

def config164SourceGroup026 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0208 index
  | 1 => NatTree.get config164SourceBlock0209 (index - 256)
  | 2 => NatTree.get config164SourceBlock0210 (index - 512)
  | 3 => NatTree.get config164SourceBlock0211 (index - 768)
  | 4 => NatTree.get config164SourceBlock0212 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0213 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0214 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0215 (index - 1792)
  | _ => none

def config164SourceGroup027 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0216 index
  | 1 => NatTree.get config164SourceBlock0217 (index - 256)
  | 2 => NatTree.get config164SourceBlock0218 (index - 512)
  | 3 => NatTree.get config164SourceBlock0219 (index - 768)
  | 4 => NatTree.get config164SourceBlock0220 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0221 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0222 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0223 (index - 1792)
  | _ => none

def config164SourceGroup028 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0224 index
  | 1 => NatTree.get config164SourceBlock0225 (index - 256)
  | 2 => NatTree.get config164SourceBlock0226 (index - 512)
  | 3 => NatTree.get config164SourceBlock0227 (index - 768)
  | 4 => NatTree.get config164SourceBlock0228 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0229 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0230 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0231 (index - 1792)
  | _ => none

def config164SourceGroup029 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0232 index
  | 1 => NatTree.get config164SourceBlock0233 (index - 256)
  | 2 => NatTree.get config164SourceBlock0234 (index - 512)
  | 3 => NatTree.get config164SourceBlock0235 (index - 768)
  | 4 => NatTree.get config164SourceBlock0236 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0237 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0238 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0239 (index - 1792)
  | _ => none

def config164SourceGroup030 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0240 index
  | 1 => NatTree.get config164SourceBlock0241 (index - 256)
  | 2 => NatTree.get config164SourceBlock0242 (index - 512)
  | 3 => NatTree.get config164SourceBlock0243 (index - 768)
  | 4 => NatTree.get config164SourceBlock0244 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0245 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0246 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0247 (index - 1792)
  | _ => none

def config164SourceGroup031 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0248 index
  | 1 => NatTree.get config164SourceBlock0249 (index - 256)
  | 2 => NatTree.get config164SourceBlock0250 (index - 512)
  | 3 => NatTree.get config164SourceBlock0251 (index - 768)
  | 4 => NatTree.get config164SourceBlock0252 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0253 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0254 (index - 1536)
  | 7 => NatTree.get config164SourceBlock0255 (index - 1792)
  | _ => none

def config164SourceGroup032 (index : Nat) : Option Nat :=
  match index / 256 with
  | 0 => NatTree.get config164SourceBlock0256 index
  | 1 => NatTree.get config164SourceBlock0257 (index - 256)
  | 2 => NatTree.get config164SourceBlock0258 (index - 512)
  | 3 => NatTree.get config164SourceBlock0259 (index - 768)
  | 4 => NatTree.get config164SourceBlock0260 (index - 1024)
  | 5 => NatTree.get config164SourceBlock0261 (index - 1280)
  | 6 => NatTree.get config164SourceBlock0262 (index - 1536)
  | _ => none

def config164SourcePage000 (index : Nat) : Option Nat :=
  match index / 2048 with
  | 0 => config164SourceGroup000 index
  | 1 => config164SourceGroup001 (index - 2048)
  | 2 => config164SourceGroup002 (index - 4096)
  | 3 => config164SourceGroup003 (index - 6144)
  | 4 => config164SourceGroup004 (index - 8192)
  | 5 => config164SourceGroup005 (index - 10240)
  | 6 => config164SourceGroup006 (index - 12288)
  | 7 => config164SourceGroup007 (index - 14336)
  | _ => none

def config164SourcePage001 (index : Nat) : Option Nat :=
  match index / 2048 with
  | 0 => config164SourceGroup008 index
  | 1 => config164SourceGroup009 (index - 2048)
  | 2 => config164SourceGroup010 (index - 4096)
  | 3 => config164SourceGroup011 (index - 6144)
  | 4 => config164SourceGroup012 (index - 8192)
  | 5 => config164SourceGroup013 (index - 10240)
  | 6 => config164SourceGroup014 (index - 12288)
  | 7 => config164SourceGroup015 (index - 14336)
  | _ => none

def config164SourcePage002 (index : Nat) : Option Nat :=
  match index / 2048 with
  | 0 => config164SourceGroup016 index
  | 1 => config164SourceGroup017 (index - 2048)
  | 2 => config164SourceGroup018 (index - 4096)
  | 3 => config164SourceGroup019 (index - 6144)
  | 4 => config164SourceGroup020 (index - 8192)
  | 5 => config164SourceGroup021 (index - 10240)
  | 6 => config164SourceGroup022 (index - 12288)
  | 7 => config164SourceGroup023 (index - 14336)
  | _ => none

def config164SourcePage003 (index : Nat) : Option Nat :=
  match index / 2048 with
  | 0 => config164SourceGroup024 index
  | 1 => config164SourceGroup025 (index - 2048)
  | 2 => config164SourceGroup026 (index - 4096)
  | 3 => config164SourceGroup027 (index - 6144)
  | 4 => config164SourceGroup028 (index - 8192)
  | 5 => config164SourceGroup029 (index - 10240)
  | 6 => config164SourceGroup030 (index - 12288)
  | 7 => config164SourceGroup031 (index - 14336)
  | _ => none

def config164SourcePage004 (index : Nat) : Option Nat :=
  match index / 2048 with
  | 0 => config164SourceGroup032 index
  | _ => none

def config164Source (index : Nat) : Option Nat :=
  match index / 16384 with
  | 0 => config164SourcePage000 index
  | 1 => config164SourcePage001 (index - 16384)
  | 2 => config164SourcePage002 (index - 32768)
  | 3 => config164SourcePage003 (index - 49152)
  | 4 => config164SourcePage004 (index - 65536)
  | _ => none

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
