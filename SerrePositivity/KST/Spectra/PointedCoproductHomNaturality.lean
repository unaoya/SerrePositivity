module

public import SerrePositivity.KST.Spectra.PointedCoproductHom
public import SerrePositivity.KST.Spectra.FunctionComplexPost
public import SerrePositivity.KST.Spectra.PointedCofiberMappingNaturality

/-!
概要：点つき余積からの Hom の関数複体表示の係数自然性。
方針：各座標で余積包含への制限の式と前後合成の可換性を使う。
規約：添字集合は固定し、Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。セルの Hom の係数自然性の積の部分。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同じ点つき源の余積の Hom の表示は係数射と可換。
方針：関数複体の評価の識別性で各包含への制限の自然性を照合する。
規約：両辺は点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §1。セルごとの群の自然な比較。 -/
@[reassoc]
lemma pointedCoproductHomIso_natural (S : Type u) (P : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap (∐ fun (_ : S) ↦ P) (Y := Y) (Z := Z) p ≫
        (pointedCoproductHomIso S P Z).hom =
      (pointedCoproductHomIso S P Y).hom ≫ SimplicialFunctionComplex.pointedPost S
        (PointedObject.basedHomMap P (Y := Y) (Z := Z) p) := by
  apply Under.UnderMorphism.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
  intro s
  change ((PointedObject.basedHomMap (∐ fun (_ : S) ↦ P) (Y := Y) (Z := Z) p).right ≫
      (pointedCoproductHomUnderlyingIso S P Z).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S (PointedObject.basedHom P Z).right s =
    ((pointedCoproductHomUnderlyingIso S P Y).hom ≫ SimplicialFunctionComplex.post S
      (PointedObject.basedHomMap P (Y := Y) (Z := Z) p).right) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S (PointedObject.basedHom P Z).right s
  rw [Category.assoc, pointedCoproductHomUnderlyingIso_eval, Category.assoc,
    SimplicialFunctionComplex.post_eval, ← Category.assoc,
    pointedCoproductHomUnderlyingIso_eval]
  exact congrArg Under.Hom.right
    (PointedMapping.prePointed_post (Limits.Sigma.ι (fun (_ : S) ↦ P) s) p).symm

end

end SerrePositivity.KST.Spectra
