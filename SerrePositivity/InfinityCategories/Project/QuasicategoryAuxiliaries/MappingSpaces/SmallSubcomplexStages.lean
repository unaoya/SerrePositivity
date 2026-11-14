module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.Logic.Small.Set

/-!
概要：小さい単体族の部分複体と、有限形状の可算段階への因子化。
方針：部分型・像・小さい和の Small 性と、有限個の非退化生成単体を使う。
規約：充填性・モデル構造・straightening に依存しない。
使われ方：Ind-S (4) の小さい内ホーン充填閉包。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 全次数で小さい二つの単体集合の間の実自然変換も同じ宇宙で小さい。 -/
lemma small_hom (A B : SSet.{v}) [∀ n, Small.{u} (A.obj n)]
    [∀ n, Small.{u} (B.obj n)] : Small.{u} (A ⟶ B) := by
  apply small_of_injective (f := fun f : A ⟶ B => fun n x => f.app n x)
  intro f g h
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact congrFun (congrFun h n) x

/-- 同じ宇宙で小さい図式の像部分複体は各次数で小さい。 -/
lemma small_range {A X : SSet.{v}} [∀ n, Small.{u} (A.obj n)]
    (f : A ⟶ X) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((SSet.Subcomplex.range f).obj n) := by
  change Small.{u} (Set.range (fun x => f.app n x))
  infer_instance

/-- 小さい個数の小さい部分複体の和は各次数で小さい。 -/
lemma small_iSup {X : SSet.{v}} {ι : Type w} [Small.{u} ι]
    (A : ι → X.Subcomplex) [∀ i n, Small.{u} ((A i).obj n)]
    (n : SimplexCategoryᵒᵖ) : Small.{u} ((⨆ i, A i).obj n) := by
  simp only [Subfunctor.iSup_obj]
  infer_instance

/-- 有限形状の像が増大列の和に入れば、同じ元の射の像は一つの段階に入る。 -/
lemma exists_range_le_stage {K X : SSet.{v}} [K.Finite]
    (A : ℕ → X.Subcomplex) (hA : Monotone A) (f : K ⟶ X)
    (hf : SSet.Subcomplex.range f ≤ ⨆ n, A n) :
    ∃ n, SSet.Subcomplex.range f ≤ A n := by
  have hs : ∀ s : K.N, ∃ n, f.app _ s.simplex ∈ (A n).obj _ := by
    intro s
    have hm := hf _ (Set.mem_range_self s.simplex)
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using hm
  let k : K.N → ℕ := fun s => (hs s).choose
  have hk (s : K.N) : f.app _ s.simplex ∈ (A (k s)).obj _ := (hs s).choose_spec
  letI : Fintype K.N := Fintype.ofFinite _
  let n := Finset.univ.sup k
  refine ⟨n, ?_⟩
  rw [← SSet.Subcomplex.image_top, ← SSet.N.iSup_subcomplex_eq_top K,
    SSet.Subcomplex.image_iSup]
  apply iSup_le
  intro s
  change (SSet.Subcomplex.ofSimplex s.simplex).image f ≤ A n
  rw [SSet.Subcomplex.image_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
  exact hA (Finset.le_sup (Finset.mem_univ s)) _ (hk s)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
