module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
概要：頂点の割当てによる codiscrete 圏の nerve への射。
方針：単体の各頂点を指定された対象に写し、一意な射で合成可能射列を作る。
規約：通常の圏の nerve と直接の境界持ち上げのみを用いる。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.6.2（Tag 01HM） の可逆な区間と貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：頂点の割当てを codiscrete 圏の nerve への射に延長する。
方針：各単体の各頂点を読み、一意な射を持つ関手にする。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な区間の構成。 -/
def codiscreteNerveMap {A : SSet.{u}} {T : Type u} (a : A _⦋0⦌ → T) :
    A ⟶ nerve (Codiscrete T) where
  app n := ↾fun s ↦ Codiscrete.functor (fun i : Fin (n.unop.len + 1) ↦
    a (A.map (SimplexCategory.const ⦋0⦌ n.unop i).op s))
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    ·
      apply congrArg Codiscrete.mk
      apply congrArg a
      change A.map (SimplexCategory.const ⦋0⦌ m.unop i).op (A.map α s) = _
      rw [← CategoryTheory.Functor.map_comp_apply]
      rfl

/-- 概要：頂点の割当てから作った射は元の割当てを実現する。
方針：零次元の唯一の単体圏の射が恒等であることを使う。
規約：対象は nerve の頂点を通常の圏の対象に戻して比較する。
使われ方：Kerodon §4.6.2（Tag 01HM） の端点の指定。 -/
lemma codiscreteNerveMap_vertex {A : SSet.{u}} {T : Type u} (a : A _⦋0⦌ → T)
    (x : A _⦋0⦌) :
    (nerveEquiv ((codiscreteNerveMap a).app (Opposite.op ⦋0⦌) x)).as = a x := by
  change a (A.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x) = a x
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h]
  change a (A.map (𝟙 (Opposite.op ⦋0⦌)) x) = a x
  rw [CategoryTheory.Functor.map_id_apply]

/-- 概要：codiscrete 圏の nerve への二つの射は頂点の割当てで決まる。
方針：自然性で各単体の各対象を零次元の像へ移す。
規約：高次単体の射は一意なので追加の整合条件は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の区間と境界の貼り合わせ。 -/
lemma codiscreteNerve_hom_ext {A : SSet.{u}} {T : Type u}
    {f g : A ⟶ nerve (Codiscrete T)}
    (h : ∀ x : A _⦋0⦌, (nerveEquiv (f.app (Opposite.op ⦋0⦌) x)).as =
      (nerveEquiv (g.app (Opposite.op ⦋0⦌) x)).as) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  ·
    have hf := ConcreteCategory.congr_hom
      (f.naturality (SimplexCategory.const ⦋0⦌ n.unop i).op) s
    have hg := ConcreteCategory.congr_hom
      (g.naturality (SimplexCategory.const ⦋0⦌ n.unop i).op) s
    have hv := h (A.map (SimplexCategory.const ⦋0⦌ n.unop i).op s)
    have hf' := congrArg (fun t : (nerve (Codiscrete T)) _⦋0⦌ ↦ (nerveEquiv t).as) hf
    have hg' := congrArg (fun t : (nerve (Codiscrete T)) _⦋0⦌ ↦ (nerveEquiv t).as) hg
    apply Codiscrete.ext
    exact hf'.symm.trans (hv.trans hg')

/-- 概要：非空の codiscrete 圏の nerve への射は任意の単射に沿って延長できる。
方針：頂点関数を単射の像の外で既定の頂点を選んで延長する。
規約：延長する単体集合は任意。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な区間の境界充填。 -/
lemma codiscreteNerve_exists_extension {A B : SSet.{u}} {T : Type u} [Nonempty T]
    (i : A ⟶ B) [Mono i] (f : A ⟶ nerve (Codiscrete T)) :
    ∃ g : B ⟶ nerve (Codiscrete T), i ≫ g = f := by
  classical
  let a : A _⦋0⦌ → T := fun x ↦ (nerveEquiv (f.app (Opposite.op ⦋0⦌) x)).as
  let b := Function.extend (i.app (Opposite.op ⦋0⦌)) a
    (fun _ ↦ Classical.choice (inferInstance : Nonempty T))
  have hi : Function.Injective (i.app (Opposite.op ⦋0⦌)) :=
    (mono_iff_injective _).mp inferInstance
  refine ⟨codiscreteNerveMap b, ?_⟩
  apply codiscreteNerve_hom_ext
  intro x
  change (nerveEquiv ((codiscreteNerveMap b).app (Opposite.op ⦋0⦌)
    (i.app (Opposite.op ⦋0⦌) x))).as = a x
  rw [codiscreteNerveMap_vertex]
  exact hi.extend_apply a _ x

/-- 概要：非空の codiscrete 圏の nerve は全境界を充填する。
方針：境界包含に沿う前の延長補題を適用する。
規約：可縮 Kan 性は既存の全境界の条件。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.6.2（Tag 01HM） の可逆な区間。 -/
lemma isContractibleKan_codiscreteNerve (T : Type u) [Nonempty T] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (nerve (Codiscrete T)) := by
  intro n f
  exact codiscreteNerve_exists_extension (boundary n).ι f

/-- 概要：可縮 Kan 複体の任意の点の包含は前合成の同値条件を満たす。
方針：点への射を trivial Kan fibration とし、切断との二対三則を使う。
規約：点は標準零単体からの任意の射。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.6.2（Tag 01HM） の可逆な区間の端点。 -/
lemma IsContractibleKan.isPrecompositionEquivalence_point {E : SSet.{u}}
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : (Δ[0] : SSet.{u}) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence e := by
  have := hE.kanComplex
  let r : E ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from E
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary r).2
    intro n
    constructor
    intro a b sq
    obtain ⟨F, hF⟩ := hE n a
    exact CommSq.HasLift.mk'
      { l := F
        fac_left := hF
        fac_right := stdSimplex.isTerminalObj₀.hom_ext _ _ }
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration r).isPrecompositionEquivalence
  apply hr.cancel_right
  have he : e ≫ r = 𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsContractibleKan (isPrecompositionEquivalence_point)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
