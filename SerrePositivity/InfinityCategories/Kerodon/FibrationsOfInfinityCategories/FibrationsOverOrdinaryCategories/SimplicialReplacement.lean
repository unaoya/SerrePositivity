module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の圏上の単体集合値図式の simplicial replacement。
方針：底の射列と始点の係数単体を組にし、始点の移動を図式の射で補う。
規約：単体集合として直接構成し、∞ 圏における余極限の存在は主張しない。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、二つの scaffold の共通の始域。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：simplicial replacement の単体の型。
方針：射列 σ と、その始点における係数値の単体を対にする。
規約：係数単体は標準単体からの射で表示する。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、scaffold の次数ごとのデータ。 -/
def simplicialReplacementSimplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (n : ℕ) : Type u :=
  Σ σ : ComposableArrows C n, ((Δ[n] : SSet.{u}) ⟶ F.obj (σ.obj 0))

/-- 概要：simplicial replacement の単体を単調写像で制限する。
方針：係数単体を制限した後、始点から新たな始点への射で運ぶ。
規約：単調写像 α の 0 の像は必ずしも 0 ではない。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、面と退化の作用。 -/
def simplicialReplacementSimplexMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {m n : SimplexCategory} (α : m ⟶ n)
    (s : simplicialReplacementSimplex F n.len) : simplicialReplacementSimplex F m.len :=
  ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ s.1,
    stdSimplex.map α ≫ s.2 ≫ F.map (s.1.map (homOfLE (Fin.zero_le _)))⟩

/-- 概要：単体集合値図式の simplicial replacement。
方針：始点での係数の輸送の恒等則と合成則を関手の法則から示す。
規約：ホーン充填性は構成の仮定に含めない。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、universal および taut scaffold の始域。 -/
@[kerodon 035V, kerodon 0365]
def simplicialReplacement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : SSet.{u} where
  obj d := simplicialReplacementSimplex F d.unop.len
  map α := ↾simplicialReplacementSimplexMap F α.unop
  map_id d := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change stdSimplex.map (𝟙 d.unop) ≫ τ ≫ F.map (σ.map (𝟙 _)) = τ
    simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change stdSimplex.map (β.unop ≫ α.unop) ≫ τ ≫
        F.map (σ.map (homOfLE _)) =
      stdSimplex.map β.unop ≫ (stdSimplex.map α.unop ≫ τ ≫
        F.map (σ.map (homOfLE _))) ≫ F.map (σ.map (homOfLE _))
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← F.map_comp, ← σ.map_comp]
    rfl

/-- 概要：simplicial replacement から底の nerve への射影。
方針：単体の対から底の射列を取り出す。
規約：係数の情報だけを忘れる。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、scaffold の底に関する可換性。 -/
@[kerodon 035V]
def simplicialReplacementProjection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : simplicialReplacement F ⟶ nerve C where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
