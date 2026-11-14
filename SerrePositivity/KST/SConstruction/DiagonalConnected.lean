module
public import SerrePositivity.KST.SConstruction.CoreSimplicial

/-! # 対角実現の連結性
概要：単体的単体集合の零段から対角への写像を構成し、零段の連結性を対角へ移す。
方針：[n]→[0] による外側の退化を全次数で用い、零単体で恒等となることを使う。
規約：BGT §7 の対角実現模型。対角の Kan 性は要求しない。
使われ方：K 空間の実現の連結性と零対象の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

/-- 概要：零段の単体集合を対角へ送る。
方針：[n]→[0] の一意な射の反対による外側の退化を n 単体で評価する。
規約：任意の単体的単体集合。使われ方：対角の全頂点を零段から得る。 -/
def diagonalZeroColumn (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    X.obj (Opposite.op ⦋0⦌) ⟶ Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X where
  app d := (X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).app d
  naturality {d e} f := by
    symm
    change (X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).app d ≫
        ((X.map f).app d ≫ (X.obj e).map f) =
      (X.obj (Opposite.op ⦋0⦌)).map f ≫
        (X.map (SimplexCategory.const e.unop ⦋0⦌ 0).op).app e
    rw [← Category.assoc, ← NatTrans.comp_app, ← X.map_comp]
    have he : (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫ f =
        (SimplexCategory.const e.unop ⦋0⦌ 0).op := by
      apply Quiver.Hom.unop_inj
      exact Subsingleton.elim _ _
    rw [he]
    exact ((X.map (SimplexCategory.const e.unop ⦋0⦌ 0).op).naturality f).symm

/-- 概要：零段から対角への写像は零単体で恒等。
方針：[0] の自己射の一意性を使う。
規約：頂点の厳密等号。使われ方：連結成分の全射性。 -/
lemma diagonalZeroColumn_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (x : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    (diagonalZeroColumn X).app (Opposite.op ⦋0⦌) x = x := by
  have he : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = 𝟙 (Opposite.op ⦋0⦌) :=
    Subsingleton.elim _ _
  change (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op).app (Opposite.op ⦋0⦌) x = x
  rw [he, X.map_id]
  rfl

/-- 概要：零段から対角への写像は連結成分で全射。
方針：全ての連結成分を頂点で代表させ、零単体での恒等性を使う。
規約：Kan 性は不要。使われ方：連結性の移送。 -/
lemma diagonalZeroColumn_piZero_surjective (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Function.Surjective (SSet.mapπ₀ (diagonalZeroColumn X)) := by
  intro a
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  refine ⟨SSet.π₀.mk x, ?_⟩
  rw [SSet.mapπ₀_mk, diagonalZeroColumn_zero]

/-- 概要：零段が前連結なら対角も前連結。
方針：零段から対角への連結成分の全射で高々一点という条件を移す。
規約：Kan 性は不要。使われ方：実現模型の連結成分。 -/
lemma diagonal_preconnected_of_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [SSet.IsPreconnected (X.obj (Opposite.op ⦋0⦌))] :
    SSet.IsPreconnected (Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := diagonalZeroColumn_piZero_surjective X a
  obtain ⟨y, rfl⟩ := diagonalZeroColumn_piZero_surjective X b
  exact congrArg (SSet.mapπ₀ (diagonalZeroColumn X)) (Subsingleton.elim x y)

/-- 概要：零段が連結なら対角も連結。
方針：前連結性を移し、零段の頂点を対角の頂点に取る。
規約：Kan 性は不要。使われ方：対角実現の連結性。 -/
lemma diagonal_connected_of_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [SSet.IsConnected (X.obj (Opposite.op ⦋0⦌))] :
    SSet.IsConnected (Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X) := by
  letI := diagonal_preconnected_of_zero X
  exact ⟨by
    obtain ⟨x⟩ := (inferInstance : (X.obj (Opposite.op ⦋0⦌)).Nonempty)
    exact ⟨x⟩⟩

/-- 概要：零対象を持つ quasicategory の単体的 core の対角は連結。
方針：零段の可縮 Kan 性から連結性を得て、零段から対角への写像で移す。
規約：安定性は不要。使われ方：K 空間の実現の連結性。 -/
instance diagonalCoreSConstruction_isConnected (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : SSet.IsConnected (diagonalCoreSConstruction C) := by
  have h := coreSConstructionZero_isContractibleKan C
  letI : SSet.IsPreconnected ((simplicialCoreSConstruction C).obj (Opposite.op ⦋0⦌)) :=
    h.piZero_subsingleton
  letI : SSet.IsConnected ((simplicialCoreSConstruction C).obj (Opposite.op ⦋0⦌)) := ⟨h.nonempty⟩
  exact diagonal_connected_of_zero (simplicialCoreSConstruction C)

end SerrePositivity.KST.SConstruction
