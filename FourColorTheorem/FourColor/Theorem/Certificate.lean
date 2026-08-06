import FourColorTheorem.FourColor.Theorem.Presentations
import FourColorTheorem.FourColor.Theorem.SemanticCertificate
import FourColorTheorem.FourColor.Presentation.Certificate

/-!
Optional bridge from the executable reducibility certificate to the
all-presentation combinatorial four-colour theorem layer.

This module imports `PresentationCertificate`, and therefore the 0--633
certificate jobs.  It is intentionally not imported by
`FourColorTheorem.FourColor`.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

/-- Coq `present.v`'s call to `not_embed_reducible`, for every one of the
633 executable configurations and in both target orientations. -/
theorem noConfigPreembeddingMinimalCounterexamples_proved :
    Presentation.NoConfigPreembeddingMinimalCounterexamples :=
  noConfigPreembeddingMinimalCounterexamples_of_semanticReducibility
    (fun {_} hmem => Config.cReducible_of_mem_theConfigs hmem)

theorem noMinimalCounterexample_of_executableCertificateAllPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations
    hconnected hshortNode heven hshortFace
    Presentation.reducibility_from_executable
    hredpart hvalid hfitMirror

theorem hypermapFourColor_of_executableCertificateAllPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificateAllPresentations
      hconnected hshortNode heven hshortFace
      hredpart hvalid hfitMirror)

theorem noMinimalCounterexample_of_executableCertificateAllPresentations_localMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hscore2 : Presentation.MirrorDscore2Transport.{u})
    (hfit : Presentation.MirrorFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_localMirror
    hconnected hshortNode heven hshortFace
    Presentation.reducibility_from_executable
    hredpart hscore2 hfit

theorem hypermapFourColor_of_executableCertificateAllPresentations_localMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hscore2 : Presentation.MirrorDscore2Transport.{u})
    (hfit : Presentation.MirrorFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificateAllPresentations_localMirror
      hconnected hshortNode heven hshortFace
      hredpart hscore2 hfit)

theorem noMinimalCounterexample_of_executableCertificateAllPresentations_plainCubicMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirror.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror
    hconnected hshortNode heven hshortFace
    Presentation.reducibility_from_executable
    hredpart hfit

theorem hypermapFourColor_of_executableCertificateAllPresentations_plainCubicMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirror.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificateAllPresentations_plainCubicMirror
      hconnected hshortNode heven hshortFace hredpart hfit)

theorem noMinimalCounterexample_of_executableCertificateAllPresentations_plainCubicMirror_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_proved
    hconnected hshortNode heven hshortFace
    Presentation.reducibility_from_executable
    hredpart

theorem hypermapFourColor_of_executableCertificateAllPresentations_plainCubicMirror_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredpart :
      Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificateAllPresentations_plainCubicMirror_proved
      hconnected hshortNode heven hshortFace hredpart)

/-- Direct no-config-fit bridge with the executable 633-configuration
certificate supplying the presentation reducibility hypothesis.  This keeps the
certificate import in this opt-in module while exposing the shortest current
route above redpart soundness. -/
theorem noMinimalCounterexample_of_executableCertificate_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hnofit :
      Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    hshortFace Presentation.reducibility_from_executable hnofit

/-- Hypermap four-colour theorem bridge using the executable certificate and
the direct no-config-fit interface. -/
theorem hypermapFourColor_of_executableCertificate_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hnofit :
      Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificate_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
      hshortFace hnofit)

/-- Face-arity form of the direct no-config-fit bridge with executable
reducibility plugged in. -/
theorem noMinimalCounterexample_of_executableCertificate_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (harity :
      Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hnofit :
      Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    harity Presentation.reducibility_from_executable hnofit

/-- Hypermap four-colour theorem bridge using face-arity, direct
no-config-fit, and the executable certificate. -/
theorem hypermapFourColor_of_executableCertificate_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (harity :
      Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hnofit :
      Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificate_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
      harity hnofit)

/-- Final interface bridge with the executable 633-configuration certificate
supplying the presentation reducibility hypothesis.  This module is optional,
so the expensive certificate jobs remain outside the lightweight
`FourColorTheorem.FourColor` build. -/
theorem noMinimalCounterexample_of_executableCertificate_interfaces_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples) :
    NoMinimalCounterexample.{0} :=
  noMinimalCounterexample_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
    hshortFace hsource hno
    Presentation.reducibility_from_executable

/-- Hypermap four-colour theorem bridge with executable reducibility plugged in.
The remaining assumptions are source validity and no-preembedding, plus the
short-face exclusion. -/
theorem hypermapFourColor_of_executableCertificate_interfaces_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples) :
    HypermapFourColorTheorem.{0} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_executableCertificate_interfaces_plainCubicMirrorUpToEleven_provedStructural
      hshortFace hsource hno)

/-- The fully instantiated universe-zero hypermap four-colour theorem. -/
theorem hypermapFourColorTheorem_zero :
    HypermapFourColorTheorem.{0} :=
  hypermapFourColorTheorem_zero_of_certificates
    Presentation.reducibility_from_executable
    (fun {_} hmem => Config.cReducible_of_mem_theConfigs hmem)

/-- The fully instantiated hypermap four-colour theorem in every universe.

The executable configurations are concrete finite data in universe zero.  An
arbitrary finite hypermap is canonically relabeled onto `Fin (card Dart)`, the
checked theorem is applied there, and the coloring is pulled back through the
resulting hypermap isomorphism. -/
theorem hypermapFourColorTheorem :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColorTheorem_of_certificates
    Presentation.reducibility_from_executable
    (fun {_} hmem => Config.cReducible_of_mem_theConfigs hmem)

end

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
