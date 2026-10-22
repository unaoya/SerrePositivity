module
public import SerrePositivity.KST.SConstruction.PointedPushoutAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-! # 同じ点つき実押し出しによる局所化単射の保存
概要：基礎単射かつ anodyne 局所化可逆な射は、同じ実押し出し後も局所化可逆。
方針：具体的な局所化単射の持ち上げ類表示を忘却後の押し出しへ適用する。
規約：もう一方の脚の単射性は要求しない。使われ方：同じ BF 候補の右包含の弱比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SerrePositivity.SimplicialModel KanTestLiftingClass

/-- 同じ点つき押し出しは、基礎局所化単射を局所化可逆な射へ送る。 -/
lemma pointedIsPushout_localized_isIso_right
    {A B C D : PointedSimplicialSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {l : B ⟶ D} {r : C ⟶ D} (h : IsPushout f g l r) [Mono f.right]
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map r.right) := by
  have hs := (Under.forget (𝟙_ SSet.{u})).map_isPushout h
  change IsPushout f.right g.right l.right r.right at hs
  have hm : localizedMonos f.right := ⟨inferInstance, hf⟩
  rw [localizedMonos_eq] at hm
  have hr := (MorphismProperty.monomorphisms SSet.{u} ⊓ rightTests.llp).of_isPushout
    hs.flip hm
  exact localized_isIso_of_llp _ hr.2

/-- 同じ実押し出しの右包含は、左脚の基礎局所化単射性から局所化可逆。 -/
lemma pointedPushout_inr_localized_isIso {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : A ⟶ C) [Mono f.right]
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pushout.inr f g).right) :=
  pointedIsPushout_localized_isIso_right (IsPushout.of_hasPushout f g) hf

end SerrePositivity.KST.SConstruction
