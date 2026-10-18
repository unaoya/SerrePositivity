module

public import SerrePositivity.KST.Spectra.PointedCofiberCoproduct
public import SerrePositivity.KST.Spectra.PointedCofiberComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：自由基点を加えた余積の射の cofiber を各セルの cofiber の余積へ移す。
方針：自由基点の余積保存の同型の自然性と cofiber の余積の普遍性を合成する。
規約：通常の単体集合の射の族を入力する。
使われ方：Goerss–Jardine VIII §1。骨格のセルごとの cofiber の分解。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance adjoinCofiberCoproductLeftAdjoint :
    (PointedObject.adjoinFunctor (C := SSet.{u})).IsLeftAdjoint :=
  PointedObject.adjoinForgetAdjunction.isLeftAdjoint

variable {S : Type u} (A : S → SSet.{u})

@[reassoc]
lemma adjoinCoproductIso_ι (s : S) :
    PointedObject.adjoinFunctor.map (Limits.Sigma.ι A s) ≫
        (PreservesCoproduct.iso PointedObject.adjoinFunctor A).hom =
      Limits.Sigma.ι (fun s ↦ PointedObject.adjoin (A s)) s :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfHasCoproductOfPreservesColimit PointedObject.adjoinFunctor A)
    (colimit.isColimit _) (Discrete.mk s)

lemma adjoinCoproductIso_natural {B : S → SSet.{u}} (i : ∀ s, A s ⟶ B s) :
    PointedObject.adjoinFunctor.map (Limits.Sigma.map i) ≫
        (PreservesCoproduct.iso PointedObject.adjoinFunctor B).hom =
      (PreservesCoproduct.iso PointedObject.adjoinFunctor A).hom ≫
        Limits.Sigma.map (fun s ↦ PointedObject.adjoinFunctor.map (i s)) := by
  apply (isColimitOfHasCoproductOfPreservesColimit PointedObject.adjoinFunctor A).hom_ext
  rintro ⟨s⟩
  change PointedObject.adjoinFunctor.map (Limits.Sigma.ι A s) ≫
      (PointedObject.adjoinFunctor.map (Limits.Sigma.map i) ≫ _) =
    PointedObject.adjoinFunctor.map (Limits.Sigma.ι A s) ≫
      ((PreservesCoproduct.iso PointedObject.adjoinFunctor A).hom ≫ _)
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Limits.Sigma.ι_map,
    CategoryTheory.Functor.map_comp, Category.assoc, adjoinCoproductIso_ι,
    ← Category.assoc, adjoinCoproductIso_ι, Limits.Sigma.ι_map]
  rfl

/-- 概要：自由基点を加えた余積の射の cofiber は個々の cofiber の余積。
方針：自由基点の余積比較で可換な正方形を作り、cofiber の同型と余積の同型を合成する。
規約：係数や射の Kan 性と単射性は不要。
使われ方：Goerss–Jardine VIII §1。各単体の境界を潰したセルの余積表示。 -/
def adjoinCofiberCoproductIso {B : S → SSet.{u}} (i : ∀ s, A s ⟶ B s) :
    pointedCofiber (PointedObject.adjoinFunctor.map (Limits.Sigma.map i)) ≅
      ∐ fun s ↦ pointedCofiber (PointedObject.adjoinFunctor.map (i s)) :=
  PointedCofiberComparison.iso _ _
    (PreservesCoproduct.iso PointedObject.adjoinFunctor A)
    (PreservesCoproduct.iso PointedObject.adjoinFunctor B) (adjoinCoproductIso_natural A i) ≪≫
      PointedCofiberCoproduct.iso (fun s ↦ PointedObject.adjoinFunctor.map (i s))

end

end SerrePositivity.KST.Spectra
