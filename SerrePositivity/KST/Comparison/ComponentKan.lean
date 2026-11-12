module

public import SerrePositivity.KST.Comparison.ComponentSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 成分全体を選んだ部分単体集合の Kan 性

概要：Kan 複体から連結成分全体を選んだ部分単体集合も Kan 複体である。
方針：元の複体でホーンを充填し、その一つの面と成分が同じなので部分複体へ戻す。
規約：KST 式 (2.2)、Lemma 2.13 の可逆成分の包含の高次比較の準備。
使われ方：選ばれた基点における正次数のホモトピー群の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial

/--
概要：選ばれた成分に属する単体を表す写像を部分単体集合へ持ち上げる。
方針：Yoneda で単体を部分型へ持ち上げる。
規約：単体の成分は最初の頂点で計算する。
使われ方：ホーン充填の部分複体への持ち上げ。
-/
def componentSimplexLift (X : SSet.{u}) (P : π₀ X → Prop) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) (h : P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv f))) :
    (Δ[n] : SSet.{u}) ⟶ (componentSubcomplex X P : SSet) :=
  yonedaEquiv.symm ⟨yonedaEquiv f, h⟩

/--
概要：単体の持ち上げは包含との合成で元の写像に戻る。
方針：Yoneda の後合成と逆写像の計算則を使う。
規約：元の写像に厳密に一致する。
使われ方：充填の各面の一致の確認。
-/
theorem componentSimplexLift_ι (X : SSet.{u}) (P : π₀ X → Prop) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) (h : P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv f))) :
    componentSimplexLift X P f h ≫ (componentSubcomplex X P).ι = f := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  change ((yonedaEquiv (yonedaEquiv.symm ⟨yonedaEquiv f, h⟩)) :
    (componentSubcomplex X P : SSet) _⦋n⦌).val = yonedaEquiv f
  rw [Equiv.apply_symm_apply]

/--
概要：一つの面が選ばれた部分複体に属するなら単体全体も属する。
方針：面への引き戻しで成分が変わらないことを使う。
規約：零次の面を含む。
使われ方：元の複体のホーン充填の成分の検査。
-/
theorem simplex_in_component_of_face (X : SSet.{u}) (P : π₀ X → Prop) {n : ℕ}
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) (i : Fin (n + 2))
    (g : (Δ[n] : SSet.{u}) ⟶ (componentSubcomplex X P : SSet))
    (h : stdSimplex.δ i ≫ f = g ≫ (componentSubcomplex X P).ι) :
    P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv f)) := by
  have he := congrArg yonedaEquiv h
  rw [stdSimplex.yonedaEquiv_δ_comp, yonedaEquiv_comp] at he
  change X.map (SimplexCategory.δ i).op (yonedaEquiv f) = (yonedaEquiv g).val at he
  have hg := (yonedaEquiv g).property
  change P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv g).val) at hg
  rw [← he, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map] at hg
  exact hg

/--
概要：Kan 複体の連結成分全体を選んだ部分単体集合は Kan である。
方針：元のホーン充填の一つの面の成分条件から充填全体を持ち上げる。
規約：選ぶ成分の性質 P は任意。
使われ方：可逆行列の成分による部分複体の高次ホモトピー群。
-/
instance componentSubcomplex_kanComplex (X : SSet.{u}) [KanComplex X]
    (P : π₀ X → Prop) : KanComplex (componentSubcomplex X P : SSet) := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain ⟨b, hb⟩ := KanComplex.hornFilling (hf.desc ≫ (componentSubcomplex X P).ι)
  have hface (j : Fin (n + 2)) (hj : j ≠ i) :
      stdSimplex.δ j ≫ b = f j hj ≫ (componentSubcomplex X P).ι := by
    calc
      _ = horn.ι i j hj ≫ (horn (n + 1) i).ι ≫ b := by rw [horn.ι_ι_assoc]
      _ = horn.ι i j hj ≫ (hf.desc ≫ (componentSubcomplex X P).ι) :=
        congrArg (fun t => horn.ι i j hj ≫ t) hb.symm
      _ = _ := by rw [← Category.assoc, hf.ι_desc]
  obtain ⟨j, hj⟩ := exists_ne i
  have hp := simplex_in_component_of_face X P b j (f j hj) (hface j hj)
  refine ⟨componentSimplexLift X P b hp, fun k hk => ?_⟩
  apply (cancel_mono (componentSubcomplex X P).ι).mp
  rw [Category.assoc, componentSimplexLift_ι]
  exact hface k hk

end SerrePositivity.KST.Comparison
