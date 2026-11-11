module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

/-!
概要：core の二次単体とホーンの辺の組み合わせ論。
方針：三角形の辺を有限に分類し、高次ホーンでは三点以外の頂点を選ぶ。
規約：退化辺も含む全ての辺を扱う。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、Corollary 4.4.3.11（Tag 01H1） の Kan 充填。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：単体の頂点への定値制限による辺は可逆。
方針：定値射を零単体経由に分解して退化辺として表す。
規約：元の単体の次数は任意。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の三角形の退化辺。 -/
lemma isInvertibleEdge_map_const {X : SSet.{u}} {n : SimplexCategory}
    (s : X.obj (Opposite.op n)) (v : Fin (n.len + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.map (SimplexCategory.const ⦋1⦌ n v).op s)) := by
  have hc : SimplexCategory.const ⦋1⦌ n v =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ n v := by rfl
  rw [hc, op_comp, X.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate _

/-- 概要：三角形への標準区間の射は面か頂点への定値射。
方針：二点から三点への単調写像を有限に判定する。
規約：三角形の三つの面を全て含む。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、core の二次単体の判定。 -/
lemma triangleEdge_cases (f : ⦋1⦌ ⟶ ⦋2⦌) :
    (∃ i : Fin 3, f = SimplexCategory.δ i) ∨
      ∃ v : Fin 3, f = SimplexCategory.const _ _ v := by
  have h : ∀ F : Fin 2 → Fin 3, Monotone F →
      (∃ i : Fin 3, F = (SimplexCategory.δ i).toOrderHom) ∨
        ∃ v : Fin 3, F = fun _ ↦ v := by decide
  rcases h f.toOrderHom f.toOrderHom.monotone with ⟨i, hi⟩ | ⟨v, hv⟩
  · left
    refine ⟨i, ?_⟩
    apply SimplexCategory.Hom.ext
    ext j
    exact congrArg Fin.val (congrFun hi j)
  · right
    refine ⟨v, ?_⟩
    apply SimplexCategory.Hom.ext
    ext j
    exact congrArg Fin.val (congrFun hv j)

/-- 概要：三角形が core に属する条件は三辺の可逆性。
方針：標準区間からの射を三面と定値射に分ける。
規約：quasicategory 性はこの判定には不要。
使われ方：Kerodon Construction 4.4.3.1（Tag 01D0）、二次ホーンの充填の保存。 -/
lemma quasicategoryCore_mem_triangle_iff {X : SSet.{u}} (s : X _⦋2⦌) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).obj (Opposite.op ⦋2⦌) ↔
      ∀ i : Fin 3, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ i s)) := by
  constructor
  · intro hs i
    exact hs (SimplexCategory.δ i)
  · intro hs f
    rcases triangleEdge_cases f with ⟨i, rfl⟩ | ⟨v, rfl⟩
    · exact hs i
    · exact isInvertibleEdge_map_const s v

/-- 概要：三次以上のホーンは全ての一単体を含む。
方針：欠ける面の頂点と辺の二頂点以外の頂点を選ぶ。
規約：外側のホーンと退化辺も含む。
使われ方：Kerodon Corollary 4.4.3.11（Tag 01H1）、高次の core の充填の保存。 -/
lemma edge_mem_horn_of_three_le (n : ℕ) (i : Fin (n + 4))
    (e : (Δ[n + 3] : SSet.{u}) _⦋1⦌) :
    e ∈ (horn (n + 3) i).obj (Opposite.op ⦋1⦌) := by
  classical
  let S : Finset (Fin (n + 4)) := {i, e 0, e 1}
  have hc : S.card < (Finset.univ : Finset (Fin (n + 4))).card := by
    have h : S.card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  apply (mem_horn_iff_notMem_range e i).2
  refine ⟨j, ?_, ?_⟩
  · intro h
    subst j
    exact hj (by simp [S])
  · rintro ⟨k, hk⟩
    fin_cases k <;> exact hj (by simp [S, ← hk])

/-- 概要：三角形の二辺が可逆なら残りの辺も可逆。
方針：ホモトピー圏で三角形の合成関係と同型の二対三性を使う。
規約：quasicategory 性は不要、ホモトピー圏の三角形関係だけを使う。
使われ方：Kerodon Corollary 4.4.3.11（Tag 01H1）、二次ホーンの新しい辺の可逆性。 -/
lemma isInvertibleEdge_triangle_missing {X : SSet.{u}} (s : X _⦋2⦌) (k : Fin 3)
    (h : ∀ i : Fin 3, i ≠ k → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ i s))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ k s)) := by
  obtain ⟨a, b, c, e, f, g, σ, rfl⟩ := SSet.Edge.CompStruct.exists_of_simplex s
  have he (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 2 σ.simplex))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 2 σ.simplex)) (f := e) σ.d₂).mp hh
  have hf (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 0 σ.simplex))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 0 σ.simplex)) (f := f) σ.d₀).mp hh
  have hg (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 1 σ.simplex))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 1 σ.simplex)) (f := g) σ.d₁).mp hh
  have hc := SSet.HomotopyCategory.homMk_comp_homMk σ
  fin_cases k
  · have : IsIso (SSet.HomotopyCategory.homMk e) := he (h 2 (by decide))
    have : IsIso (SSet.HomotopyCategory.homMk g) := hg (h 1 (by decide))
    have : IsIso (SSet.HomotopyCategory.homMk e ≫ SSet.HomotopyCategory.homMk f) := by
      rw [hc]
      infer_instance
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f := IsIso.of_isIso_comp_left
      (SSet.HomotopyCategory.homMk e) (SSet.HomotopyCategory.homMk f)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 0 σ.simplex)) (f := f) σ.d₀).mpr this
  · have : IsIso (SSet.HomotopyCategory.homMk e) := he (h 2 (by decide))
    have : IsIso (SSet.HomotopyCategory.homMk f) := hf (h 0 (by decide))
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge g := by
      change IsIso (SSet.HomotopyCategory.homMk g)
      rw [← hc]
      infer_instance
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 1 σ.simplex)) (f := g) σ.d₁).mpr this
  · have : IsIso (SSet.HomotopyCategory.homMk f) := hf (h 0 (by decide))
    have : IsIso (SSet.HomotopyCategory.homMk g) := hg (h 1 (by decide))
    have : IsIso (SSet.HomotopyCategory.homMk e ≫ SSet.HomotopyCategory.homMk f) := by
      rw [hc]
      infer_instance
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := IsIso.of_isIso_comp_right
      (SSet.HomotopyCategory.homMk e) (SSet.HomotopyCategory.homMk f)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ 2 σ.simplex)) (f := e) σ.d₂).mpr this

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
