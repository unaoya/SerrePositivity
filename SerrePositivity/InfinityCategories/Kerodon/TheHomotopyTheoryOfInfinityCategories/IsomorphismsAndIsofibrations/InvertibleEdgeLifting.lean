module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FibrationRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornJoin
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：ホモトピー圏で可逆な辺と外側ホーンの充填条件。
方針：左右ファイブレーションの三角形の持ち上げと join によるホーンの表示を使う。
規約：外側ホーンの条件は次数二以上で、指定した最初又は最後の辺を固定する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F）、§4.4.3（Tag 01CZ）、HTT Proposition 1.2.4.3。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：辺のホモトピー圏での可逆性。
方針：辺の生成する射に通常の IsIso を課す。
規約：定義自体には quasicategory 性は不要。
使われ方：HTT Proposition 1.2.4.3、Kerodon Theorem 4.4.2.6（Tag 019F） の第一条件。 -/
@[kerodon 004R, kerodon 019F]
abbrev IsInvertibleEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Prop :=
  IsIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 概要：単体からその始点・終点を持つ辺を作る。
方針：両端を面写像の値として定義する。
規約：追加の端点の選択は不要。
使われ方：HTT §1.2.4 の標準辺の像の表示。 -/
def edgeOfSimplex {X : SSet.{u}} (s : X _⦋1⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) (X.δ 1 s) (X.δ 0 s) := ⟨s, rfl, rfl⟩

/-- 概要：同じ一単体を表す辺は可逆性も同じ。
方針：一単体の等式から端点の等式を取り、辺の証明の無関係性を使う。
規約：端点の表示が異なる場合にも使える。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の指定された辺と射影した辺の比較。 -/
lemma isInvertibleEdge_congr {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y'} (h : e.edge = f.edge) :
    IsInvertibleEdge e ↔ IsInvertibleEdge f := by
  have hx : x = x' := e.src_eq.symm.trans
    ((congrArg (fun s : X _⦋1⦌ ↦ X.δ 1 s) h).trans f.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans
    ((congrArg (fun s : X _⦋1⦌ ↦ X.δ 0 s) h).trans f.tgt_eq)
  subst x'
  subst y'
  have hef : e = f := SSet.Truncated.Edge.ext h
  rw [hef]

/-- 概要：零番目の外側ホーンに含まれる最初の辺。
方針：標準単体の 0→1 の辺をホーンの部分型へ持ち上げる。
規約：ホーンの次元は n+2。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の第二条件の固定する辺。 -/
def initialHornEdge (n : ℕ) : (horn (n + 2) 0 : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)

/-- 概要：最後の外側ホーンに含まれる最後の辺。
方針：標準単体の n+1→n+2 の辺をホーンの部分型へ持ち上げる。
規約：ホーンの次元は n+2。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の第三条件の固定する辺。 -/
def finalHornEdge (n : ℕ) : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) (Fin.last (n + 2)) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
    (Fin.le_last _)
    (by
      have hs : ({Fin.last (n + 2), (⟨n + 1, by omega⟩ : Fin (n + 3)),
          Fin.last (n + 2)} : Finset _) = {⟨n + 1, by omega⟩, Fin.last (n + 2)} := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hs]
      exact Finset.card_le_two.trans (show 2 ≤ n + 2 by omega))

/-- 概要：e を最初の辺に持つ全ての外側ホーンの充填条件。
方針：次数二以上の全てのホーンを量化する。
規約：辺の等式は一単体としての等式。
使われ方：HTT Proposition 1.2.4.3、Kerodon Theorem 4.4.2.6（Tag 019F） の第二条件。 -/
def HasInitialHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Prop :=
  ∀ (n : ℕ) (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X),
    σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = e.edge →
      ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X, (horn (n + 2) 0).ι ≫ F = σ

/-- 概要：e を最後の辺に持つ全ての外側ホーンの充填条件。
方針：次数二以上の全てのホーンを量化する。
規約：最初のホーンの条件とは独立に定義する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の第三条件。 -/
def HasFinalHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Prop :=
  ∀ (n : ℕ) (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X),
    σ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = e.edge →
      ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X, (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = σ

/-- 概要：Kan 複体の任意の辺は最初の外側ホーンの充填条件を満たす。
方針：全てのホーンを充填できるという定義を適用する。
規約：指定する辺の条件を追加しても充填は可能。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D） の Kan 側。 -/
lemma hasInitialHornFillers_of_kanComplex {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    HasInitialHornFillers e := by
  intro n σ _
  obtain ⟨F, hF⟩ := KanComplex.hornFilling σ
  exact ⟨F, hF.symm⟩

/-- 概要：Kan 複体の任意の辺は最後の外側ホーンの充填条件を満たす。
方針：全てのホーンを充填できるという定義を適用する。
規約：次数二以上の最後のホーンを扱う。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D） の Kan 側。 -/
lemma hasFinalHornFillers_of_kanComplex {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    HasFinalHornFillers e := by
  intro n σ _
  obtain ⟨F, hF⟩ := KanComplex.hornFilling σ
  exact ⟨F, hF.symm⟩

/-- 概要：可逆な辺の像は可逆。
方針：ホモトピー圏の関手は同型を保つ。
規約：quasicategory 性は不要。
使われ方：HTT §1.2.4、Kerodon §4.4（Tag 01EM） の可逆性の関手性。 -/
lemma IsInvertibleEdge.map {X Y : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (he : IsInvertibleEdge e) (q : X ⟶ Y) : IsInvertibleEdge (e.map ((truncation 2).map q)) := by
  have := he
  exact (hoFunctor.map q).toFunctor.map_isIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 概要：quasicategory のホモトピー圏の射は一本の辺で表せる。
方針：A1 の比較同値を通じて辺のホモトピー類の代表元を選ぶ。
規約：零単体で表示した二対象の間の全ての射を扱う。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の逆射の辺による表示。 -/
lemma homotopyCategory_homMk_surjective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Surjective
      (SSet.Truncated.HomotopyCategory.homMk :
        SSet.Truncated.Edge (X := (truncation 2).obj X) x y →
          (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)) := by
  intro m
  obtain ⟨a, ha⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor.map_surjective
    (X := HomotopyCategory₂.mk (A := (truncation 2).obj X) x)
    (Y := HomotopyCategory₂.mk (A := (truncation 2).obj X) y) m
  obtain ⟨e, rfl⟩ := HomotopyCategory₂.homMk_surjective a
  exact ⟨e, ha⟩

/-- 概要：ホモトピー圏での辺の合成の等式は実際の合成三角形で表せる。
方針：比較同値で辺のホモトピー類の圏へ戻し、二切断の充填補題を使う。
規約：仮定は quasicategory 性のみ。
使われ方：HTT §1.2.3、Kerodon §4.4（Tag 01EM） の可逆辺の三角形の構成。 -/
lemma compStruct_nonempty_of_homMk_fac {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (fac : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g = SSet.Truncated.HomotopyCategory.homMk h) :
    Nonempty (SSet.Truncated.Edge.CompStruct f g h) := by
  apply SSet.Truncated.Edge.CompStruct.nonempty_iff.2
  have hfac := congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X)).map k) fac
  simpa only [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
    SSet.Truncated.HomotopyCategory.lift_map_homMk] using hfac

/-- 概要：可逆な辺には両側の逆を証明する実際の二つの三角形がある。
方針：ホモトピー圏の逆射を一本の辺で表し、合成の等式を三角形に直す。
規約：両側で同じ逆辺を使う。
使われ方：HTT §1.2.4、Kerodon Theorem 4.4.2.6（Tag 019F） の充填の準備。 -/
@[kerodon 004V]
lemma IsInvertibleEdge.nonempty_inverse {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (he : IsInvertibleEdge e) :
    Nonempty (Σ g : SSet.Truncated.Edge (X := (truncation 2).obj X) y x,
      SSet.Truncated.Edge.CompStruct e g
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) ×
      SSet.Truncated.Edge.CompStruct g e
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y)) := by
  have := he
  obtain ⟨g, hg⟩ := homotopyCategory_homMk_surjective y x
    (inv (SSet.Truncated.HomotopyCategory.homMk e))
  have h₁ : SSet.Truncated.HomotopyCategory.homMk e ≫
      SSet.Truncated.HomotopyCategory.homMk g =
      SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) := by
    rw [hg, IsIso.hom_inv_id, SSet.Truncated.HomotopyCategory.homMk_id]
  have h₂ : SSet.Truncated.HomotopyCategory.homMk g ≫
      SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y) := by
    rw [hg, IsIso.inv_hom_id, SSet.Truncated.HomotopyCategory.homMk_id]
  obtain ⟨t₁⟩ := compStruct_nonempty_of_homMk_fac h₁
  obtain ⟨t₂⟩ := compStruct_nonempty_of_homMk_fac h₂
  exact ⟨g, t₁, t₂⟩

/-- 概要：左ファイブレーションは三角形の最初の辺と対角を固定して持ち上げる。
方針：二次の零番目ホーンを二つの辺の pushout で作り、その rlp を使う。
規約：標的の三角形と全く同じ三角形の上に持ち上げる。
使われ方：HTT Proposition 2.1.1.5、Kerodon Proposition 4.4.2.11（Tag 019K） の可逆辺の反映。 -/
lemma leftFibration_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₁)
    (h : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₂)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₁) (q.app (Opposite.op ⦋0⦌) x₂))
    (t : SSet.Truncated.Edge.CompStruct (f.map ((truncation 2).map q)) g
      (h.map ((truncation 2).map q))) :
    Nonempty (Σ g' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂,
      {t' : SSet.Truncated.Edge.CompStruct f g' h //
        q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex}) := by
  obtain ⟨a, ha₁, ha₂⟩ := horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm h.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (f.src_eq.trans h.src_eq.symm))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin 3) (by decide))
  have sq : CommSq a (horn 2 0).ι q (SSet.yonedaEquiv.symm t.simplex) := by
    constructor
    apply horn₂₀.isPushout.hom_ext
    · simp only [← Category.assoc, ha₁, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₂.symm
    · simp only [← Category.assoc, ha₂, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₁.symm
  let F := sq.lift
  have hF₂ : stdSimplex.δ 2 ≫ F = SSet.yonedaEquiv.symm f.edge := by
    rw [← horn.ι_ι_assoc 0 2 (by decide), sq.fac_left, ha₁]
    rfl
  have hF₁ : stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm h.edge := by
    rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left, ha₂]
    rfl
  let s := SSet.yonedaEquiv F
  have h₂ : X.δ 2 s = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₂]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have h₁ : X.δ 1 s = h.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁]
    exact SSet.yonedaEquiv.apply_symm_apply h.edge
  have hsrc : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) = x₁ := by
    have he : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) =
        X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₂]
    exact f.tgt_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) s) = x₂ := by
    have he : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) s) =
        X.δ (0 : Fin 2) (X.δ (1 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₁]
    exact h.tgt_eq
  let g' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂ :=
    ⟨X.δ 0 s, hsrc, htgt⟩
  refine ⟨g', ⟨⟨s, h₂, rfl, h₁⟩, ?_⟩⟩
  change q.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv sq.lift) = _
  rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

/-- 概要：左ファイブレーションは可逆な像を持つ辺の可逆性を反映する。
方針：像の逆三角形を持ち上げて片側逆を作り、その辺でも同じ構成を繰り返す。
規約：X,Y は quasicategory。相対的な二次の零番目ホーンだけを使う。
使われ方：HTT Proposition 2.1.1.5、Kerodon Proposition 4.4.2.11（Tag 019K）。 -/
@[kerodon 019K]
lemma leftFibration_reflects_invertibleEdge {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : IsInvertibleEdge (e.map ((truncation 2).map q))) : IsInvertibleEdge e := by
  have split {a b : X _⦋0⦌}
      (f : SSet.Truncated.Edge (X := (truncation 2).obj X) a b)
      (hf : IsInvertibleEdge (f.map ((truncation 2).map q))) :
      ∃ g : SSet.Truncated.Edge (X := (truncation 2).obj X) b a,
        SSet.Truncated.HomotopyCategory.homMk f ≫
          SSet.Truncated.HomotopyCategory.homMk g = 𝟙 _ ∧
        IsInvertibleEdge (g.map ((truncation 2).map q)) := by
    obtain ⟨g, t₁, t₂⟩ := IsInvertibleEdge.nonempty_inverse hf
    have t : SSet.Truncated.Edge.CompStruct (f.map ((truncation 2).map q)) g
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj X) a).map ((truncation 2).map q)) := by
      simpa only [SSet.Truncated.Edge.map_id] using t₁
    obtain ⟨g', t', ht'⟩ := leftFibration_liftCompStruct q f
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) a) g t
    have hg' : g'.map ((truncation 2).map q) = g := by
      apply SSet.Truncated.Edge.ext
      change q.app (Opposite.op ⦋1⦌) g'.edge = g.edge
      rw [← t'.d₀]
      calc
        _ = Y.δ 0 (q.app (Opposite.op ⦋2⦌) t'.simplex) :=
          ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op) t'.simplex
        _ = g.edge := by rw [ht']; exact t.d₀
    refine ⟨g', ?_, ?_⟩
    · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t'
    · rw [hg']
      refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map q)), ?_, ?_⟩⟩
      · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₂
      · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₁
  obtain ⟨g, hg, hqg⟩ := split e he
  obtain ⟨k, hk, _⟩ := split g hqg
  have heq : SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk k := by
    calc
      _ = SSet.Truncated.HomotopyCategory.homMk e ≫
          (SSet.Truncated.HomotopyCategory.homMk g ≫
            SSet.Truncated.HomotopyCategory.homMk k) := by rw [hk, Category.comp_id]
      _ = (SSet.Truncated.HomotopyCategory.homMk e ≫
          SSet.Truncated.HomotopyCategory.homMk g) ≫
            SSet.Truncated.HomotopyCategory.homMk k := (Category.assoc _ _ _).symm
      _ = SSet.Truncated.HomotopyCategory.homMk k := by rw [hg, Category.id_comp]
  exact ⟨⟨SSet.Truncated.HomotopyCategory.homMk g, hg, by rw [heq]; exact hk⟩⟩

/-- 概要：左ファイブレーションは辺を指定された始点から持ち上げる。
方針：一次の零番目ホーンに定数射を置いて rlp を使う。
規約：終点の持ち上げは出力として決まる。
使われ方：HTT §2.1.1、Kerodon §4.4（Tag 01EM） の可逆辺の終点を固定した持ち上げの準備。 -/
lemma leftFibration_liftEdge_source {X Y : SSet.{u}} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (x : X _⦋0⦌) {y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x) y) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm x ∧
      F ≫ q = SSet.yonedaEquiv.symm e.edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin 2) (by decide))
  have sq : CommSq (SSet.const x) (horn 1 0).ι q (SSet.yonedaEquiv.symm e.edge) := by
    constructor
    apply horn.hom_ext'
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (SSet.yonedaEquiv_symm_zero _).symm.trans
        (congrArg SSet.yonedaEquiv.symm e.src_eq.symm)
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left, SSet.comp_const,
    SSet.yonedaEquiv_symm_zero]

/-- 概要：左ファイブレーションは可逆な辺を指定された終点へ持ち上げる。
方針：逆辺を終点から持ち上げ、逆の三角形を零番目の二次ホーンとして持ち上げ直す。
規約：下の辺をホモトピーで置き換えず、そのままの辺を持ち上げる。
使われ方：Kerodon Example 4.4.1.11（Tag 01EW）、Proposition 4.4.2.13（Tag 01H0） の最後の辺を持つホーン。 -/
lemma leftFibration_liftInvertibleEdge_target {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] {a : Y _⦋0⦌} (b : X _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) a (q.app (Opposite.op ⦋0⦌) b))
    (he : IsInvertibleEdge e) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm b ∧
      F ≫ q = SSet.yonedaEquiv.symm e.edge := by
  obtain ⟨g, _, tg⟩ := IsInvertibleEdge.nonempty_inverse he
  obtain ⟨G, hG₁, hGq⟩ := leftFibration_liftEdge_source q b g
  let v := SSet.yonedaEquiv G
  have hv₁ : X.δ 1 v = b := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hG₁, Equiv.apply_symm_apply]
  have hvq : q.app (Opposite.op ⦋1⦌) v = g.edge := by
    rw [← SSet.yonedaEquiv_comp, hGq]
    exact SSet.yonedaEquiv.apply_symm_apply g.edge
  let z := X.δ 0 v
  let g' : SSet.Truncated.Edge (X := (truncation 2).obj X) b z := ⟨v, hv₁, rfl⟩
  have hz : q.app (Opposite.op ⦋0⦌) z = a := by
    calc
      _ = Y.δ 0 (q.app (Opposite.op ⦋1⦌) v) :=
        ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op) v
      _ = a := by rw [hvq]; exact g.tgt_eq
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) z) (q.app (Opposite.op ⦋0⦌) b) :=
    ⟨e.edge, e.src_eq.trans hz.symm, e.tgt_eq⟩
  have hid : ((SSet.Truncated.Edge.id (X := (truncation 2).obj X) b).map
      ((truncation 2).map q)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Y)
        (q.app (Opposite.op ⦋0⦌) b)).edge :=
    congrArg SSet.Truncated.Edge.edge (SSet.Truncated.Edge.map_id b ((truncation 2).map q))
  let t : SSet.Truncated.Edge.CompStruct (g'.map ((truncation 2).map q)) e'
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj X) b).map ((truncation 2).map q)) :=
    ⟨tg.simplex, tg.d₂.trans hvq.symm, tg.d₀, tg.d₁.trans hid.symm⟩
  obtain ⟨k, tk, htk⟩ := leftFibration_liftCompStruct q g'
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) b) e' t
  have hkq : q.app (Opposite.op ⦋1⦌) k.edge = e.edge := by
    rw [← tk.d₀]
    calc
      _ = Y.δ 0 (q.app (Opposite.op ⦋2⦌) tk.simplex) :=
        ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op) tk.simplex
      _ = e.edge := by rw [htk]; exact t.d₀
  refine ⟨SSet.yonedaEquiv.symm k.edge, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm k.tgt_eq
  · rw [SSet.yonedaEquiv_symm_comp, hkq]
    rfl

/-- 概要：左ファイブレーションの下の辺が可逆なら一次の最後のホーンを持ち上げられる。
方針：固定された終点を Yoneda で読み、終点を固定した可逆辺の持ち上げを適用する。
規約：下の射も上の点もそのまま保つ。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0） の coslice の一次ホーンへの帰着。 -/
lemma leftFibration_liftHorn_one_last {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (a : (horn 1 1 : SSet.{u}) ⟶ X)
    (b : (Δ[1] : SSet.{u}) ⟶ Y) (sq : CommSq a (horn 1 1).ι q b)
    (hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv b))) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X, (horn 1 1).ι ≫ F = a ∧ F ≫ q = b := by
  let x := SSet.yonedaEquiv (horn.ι (1 : Fin 2) 0 (by decide) ≫ a)
  let s := SSet.yonedaEquiv b
  have ht : Y.δ 0 s = q.app (Opposite.op ⦋0⦌) x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp,
      ← horn.ι_ι_assoc (1 : Fin 2) 0 (by decide), ← sq.w, ← Category.assoc,
      SSet.yonedaEquiv_comp]
  let e : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (Y.δ 1 s) (q.app (Opposite.op ⦋0⦌) x) := ⟨s, rfl, ht⟩
  have he : IsInvertibleEdge e := (isInvertibleEdge_congr (e := edgeOfSimplex s) (f := e) rfl).1 hb
  obtain ⟨F, hF₀, hFq⟩ := leftFibration_liftInvertibleEdge_target q x e he
  refine ⟨F, ?_, ?_⟩
  · apply horn.hom_ext'
    intro j hj
    fin_cases j
    · rw [horn.ι_ι_assoc]
      change stdSimplex.δ (0 : Fin 2) ≫ F = horn.ι (1 : Fin 2) 0 (by decide) ≫ a
      rw [hF₀]
      exact SSet.yonedaEquiv.symm_apply_apply _
    · exact (hj rfl).elim
  · exact hFq.trans (SSet.yonedaEquiv.symm_apply_apply b)

/-- 概要：右因子の辺が可逆なら、最後の頂点と任意の部分図式の pushout-join から延長できる。
方針：coslice の制限の左ファイブレーションに一次の最後のホーンを持ち上げ、uncurry する。
規約：左因子とその部分複体は任意。可逆性は右の辺にだけ課す。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0）、HTT Proposition 1.2.4.3 の join 表示。 -/
lemma joinUnion_extend_of_invertible_rightEdge {K X : SSet.{u}} [Quasicategory X]
    (K₀ : K.Subcomplex) (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion K₀ (horn 1 1) : SSet.{u}) ⟶ X)
    (he : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (K₀ : SSet.{u}) Δ[1] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft K₀ (horn 1 1) ≫ T)))) :
    ∃ L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[1] : SSet.{u}) ⟶ X, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion K₀ (horn 1 1)).ι ≫ L = T := by
  let B₀ : (Δ[1] : SSet.{u}).Subcomplex := horn 1 1
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout K₀ B₀
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft K₀ B₀ ≫ T
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight K₀ B₀ ≫ T
  have hover : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (K₀ : SSet.{u})) B₀.ι ≫ G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap K₀.ι (𝟙 (B₀ : SSet.{u})) ≫ H := by
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ T) hs.w
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (B₀ : SSet.{u}) ≫ H
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (K₀ : SSet.{u}) Δ[1] ≫ G = K₀.ι ≫ p := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (K₀ : SSet.{u}) (B₀ : SSet.{u}) ≫ z) hover
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at h
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (K₀ : SSet.{u}) (B₀ : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap K₀.ι (𝟙 (B₀ : SSet.{u}))) H, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc] at h
    exact h
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry G hG
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry H (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (B₀ : SSet.{u}) ≫ H = p from rfl)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p K₀.ι
  have sq : CommSq b B₀.ι q a := by
    constructor
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (K₀.ι ≫ p)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact hover.symm
  have hmap : IsInvertibleEdge ((edgeOfSimplex (SSet.yonedaEquiv a)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (K₀.ι ≫ p)))) := by
    have hc : ((edgeOfSimplex (SSet.yonedaEquiv a)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (K₀.ι ≫ p)))).edge =
        (edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (K₀ : SSet.{u}) Δ[1] ≫ G))).edge := by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (K₀.ι ≫ p)).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv a) = _
      rw [← SSet.yonedaEquiv_comp]
      exact congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection G hG)
    exact (isInvertibleEdge_congr hc).2 he
  have ha : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv a)) :=
    leftFibration_reflects_invertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (K₀.ι ≫ p)) _ hmap
  obtain ⟨F, hF₁, hFq⟩ := leftFibration_liftHorn_one_last q b a sq ha
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry F, ?_⟩
  apply hs.hom_ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft K₀ B₀ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion K₀ B₀).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry F) = G
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι]
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry hFq
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry] at h
    exact h
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight K₀ B₀ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion K₀ B₀).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry F) = H
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι]
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry hF₁
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry] at h
    exact h

/-- 概要：可逆な辺を最後の辺に持つ外側ホーンは全て充填できる。
方針：外側ホーンを境界と辺の pushout-join と同定し、coslice の制限に沿い可逆辺を持ち上げる。
規約：全ての次数二以上を扱い、指定された辺をそのまま保つ。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇒(3)、HTT Proposition 1.2.4.3 の双対。 -/
@[kerodon 019F]
lemma hasFinalHornFillers_of_isInvertibleEdge {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : IsInvertibleEdge e) : HasFinalHornFillers e := by
  intro n σ hσ
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornJoinIso n).hom ≫ σ
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) Δ[1] ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (horn 1 1) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornJoinIso n).hom
  have hR : R ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom := by
    dsimp only [R]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornJoinIso_hom_ι,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (horn 1 1))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary n) (horn 1 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  have hr : SSet.yonedaEquiv R = finalHornEdge n := by
    apply Subtype.ext
    change (horn (n + 2) (Fin.last (n + 2))).ι.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv R) = _
    rw [← SSet.yonedaEquiv_comp, hR]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.joinStdSimplexIso_inr_edge n
  have hEdge : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) Δ[1] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (horn 1 1) ≫ T))) := by
    have hc : (edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) Δ[1] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (horn 1 1) ≫ T))).edge = e.edge := by
      change SSet.yonedaEquiv (R ≫ σ) = e.edge
      rw [SSet.yonedaEquiv_comp, hr, hσ]
    exact (isInvertibleEdge_congr hc).2 he
  obtain ⟨L, hL⟩ := joinUnion_extend_of_invertible_rightEdge (boundary n) T hEdge
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv ≫ L, ?_⟩
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornJoinIso n).hom).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id_assoc]
  exact hL

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
