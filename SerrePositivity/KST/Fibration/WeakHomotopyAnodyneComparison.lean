module
public import SerrePositivity.KST.Fibration.InitialVertexLocalizedContraction
public import SerrePositivity.InfinityCategories.F2.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.WeakWhitehead

/-! # Kan 標的による弱同値を同じ射の anodyne 局所化可逆性へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の弱同値の連続 Kan 置換の実逆と、同じ単位の自然性で元の射の可逆性を得る。 -/
theorem weakHomotopyEquivalence_anodyneQ_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f) : IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hR := F2.continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have : IsIso (Q.map (F2.continuousKanReplacement.map f)) :=
    homotopyEquivalence_anodyneQ_isIso _ hR.isSimplicialHomotopyEquivalence
  have : IsIso (Q.map (F2.continuousKanReplacementUnit.app X)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne X)
  have : IsIso (Q.map (F2.continuousKanReplacementUnit.app Y)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne Y)
  have hn := congrArg Q.map (F2.continuousKanReplacementUnit.naturality f)
  change Q.map (f ≫ F2.continuousKanReplacementUnit.app Y) =
    Q.map (F2.continuousKanReplacementUnit.app X ≫ F2.continuousKanReplacement.map f) at hn
  rw [Q.map_comp, Q.map_comp] at hn
  have hc : IsIso (Q.map f ≫ Q.map (F2.continuousKanReplacementUnit.app Y)) :=
    hn.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Fibration
