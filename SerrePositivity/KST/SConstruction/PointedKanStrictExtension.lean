module
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison

/-! # Kan 標的への点つき射の Kan 単位に沿う厳密な延長
概要：Kan 標的への点つき射は、源の既存の Kan 置換単位に沿って厳密に延長できる。
方針：anodyne な単位を標的の終射に持ち上げ、単位が基点を保つ式で延長を点つきにする。
規約：延長の可逆性は元の射が局所化同型のときに証明する。使われ方：零行 fiber 比較の π_*。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.SimplicialModel

/-- Kan 標的への点つき射は既存の源の Kan 単位に沿って厳密に延長できる。 -/
lemma exists_pointedKanStrictExtension {A B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : A ⟶ B) : ∃ g : Spectra.PointedKanReplacement.obj A ⟶ B,
      Spectra.PointedKanReplacement.unit.app A ≫ g = f := by
  let i := Spectra.PointedKanReplacement.unit.app A
  have hp : SSet.modelCategoryQuillen.J.rlp (terminal.from B.right) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  let : HasLiftingProperty i.right (terminal.from B.right) :=
    (Spectra.PointedKanReplacement.unit_anodyne A) _ hp
  let sq : CommSq f.right i.right (terminal.from B.right)
      (terminal.from (Spectra.PointedKanReplacement.obj A).right) :=
    ⟨terminal.hom_ext _ _⟩
  let g : Spectra.PointedKanReplacement.obj A ⟶ B := Under.homMk sq.lift (by
    have hi : A.hom ≫ i.right = (Spectra.PointedKanReplacement.obj A).hom := Under.w i
    have hf : A.hom ≫ f.right = B.hom := Under.w f
    rw [← hi, Category.assoc, sq.fac_left, hf])
  refine ⟨g, ?_⟩
  apply Under.UnderMorphism.ext
  exact sq.fac_left

/-- 既存の Kan 単位に沿って選んだ点つきの厳密な延長。 -/
def pointedKanStrictExtension {A B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : A ⟶ B) : Spectra.PointedKanReplacement.obj A ⟶ B :=
  (exists_pointedKanStrictExtension f).choose

/-- 選んだ点つき Kan 延長は元の射を厳密に回収する。 -/
lemma pointedKanStrictExtension_fac {A B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : A ⟶ B) : Spectra.PointedKanReplacement.unit.app A ≫ pointedKanStrictExtension f = f :=
  (exists_pointedKanStrictExtension f).choose_spec

/-- 元の点つき射が局所化同型なら、Kan 標的への厳密な延長は全基点 π_* 同型。 -/
lemma pointedKanStrictExtension_piIsomorphism {A B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedKanStrictExtension f).right := by
  let Q := AnodyneHomotopy.anodyneQ
  have hi : IsIso (Q.map (Spectra.PointedKanReplacement.unit.app A).right) :=
    (Localization.inverts Q anodyneExtensions) _ (Spectra.PointedKanReplacement.unit_anodyne A)
  have he : Q.map (Spectra.PointedKanReplacement.unit.app A).right ≫
      Q.map (pointedKanStrictExtension f).right = Q.map f.right :=
    (Q.map_comp _ _).symm.trans
      (congrArg Q.map (congrArg Under.Hom.right (pointedKanStrictExtension_fac f)))
  have hc : IsIso (Q.map (Spectra.PointedKanReplacement.unit.app A).right ≫
      Q.map (pointedKanStrictExtension f).right) := he.symm ▸ hf
  exact kanPiIsomorphism_of_localized_isIso (pointedKanStrictExtension f).right
    ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.KST.SConstruction
