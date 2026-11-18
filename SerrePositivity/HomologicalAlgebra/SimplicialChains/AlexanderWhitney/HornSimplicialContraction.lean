module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 標準ホーンの頂点への単体的収縮

概要：正の次元の標準ホーンを欠けた面の対頂点へ収縮する。
方針：min(-,i) から恒等と定値への二つの円柱を作る。
規約：円柱の頂点は元の単体の頂点と i のみ。モデル構造を使わない。
使われ方：Sp の β6 f4c の元の正規化ホーン包含の弱同値性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.SimplicialChains.AlexanderWhitney
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open scoped _root_.Simplicial
variable (n : ℕ) (i : Fin (n + 2))

/-- 概要：ホーン円柱の各単体の単調写像。
方針：区間の値で min と終端写像を切り替える。規約：元の順序を保持。
使われ方：hornContractionPrism の成分。 -/
def hornPrismOrder (b : Bool) {m : SimplexCategoryᵒᵖ}
    (x : (horn (n + 1) i : SSet.{u}).obj m) (t : (Δ[1] : SSet.{u}).obj m) :
    Fin (m.unop.len + 1) →o Fin (n + 2) where
  toFun a := if stdSimplex.asOrderHom t a = 0 then
    min (stdSimplex.asOrderHom x.val a) i else
    if b then stdSimplex.asOrderHom x.val a else i
  monotone' := by
    intro a c hac
    have hxc := (stdSimplex.asOrderHom x.val).monotone hac
    have htc := (stdSimplex.asOrderHom t).monotone hac
    by_cases ha : stdSimplex.asOrderHom t a = 0 <;>
      by_cases hc : stdSimplex.asOrderHom t c = 0 <;> simp only [ha, hc, ite_true, ite_false]
    · exact min_le_min hxc le_rfl
    · cases b
      · exact min_le_right _ _
      · exact le_trans (min_le_left _ _) hxc
    · have : stdSimplex.asOrderHom t a = 0 := le_antisymm (hc ▸ htc) (Fin.zero_le _)
      contradiction
    · cases b
      · exact le_rfl
      · exact hxc

/-- 概要：円柱の各単体は元のホーンに留まる。
方針：像の頂点が元の像と i の和集合に含まれることを使う。
規約：全単体で成立。使われ方：円柱の値域条件。 -/
lemma hornPrism_mem (b : Bool) {m : SimplexCategoryᵒᵖ}
    (x : (horn (n + 1) i : SSet.{u}).obj m) (t : (Δ[1] : SSet.{u}).obj m) :
    stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrismOrder n i b x t)) ∈
      (horn (n + 1) i).obj m := by
  change Set.range (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrismOrder n i b x t) ∪ {i} ≠ Set.univ
  intro he
  apply x.property
  apply Set.eq_univ_of_forall
  intro j
  have hj := Set.eq_univ_iff_forall.mp he j
  rcases hj with ⟨a, rfl⟩ | hj
  · have hval : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrismOrder n i b x t a = stdSimplex.asOrderHom x.val a ∨
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrismOrder n i b x t a = i := by
      change (if stdSimplex.asOrderHom t a = 0 then min (stdSimplex.asOrderHom x.val a) i
        else if b then stdSimplex.asOrderHom x.val a else i) = stdSimplex.asOrderHom x.val a ∨
        (if stdSimplex.asOrderHom t a = 0 then min (stdSimplex.asOrderHom x.val a) i
        else if b then stdSimplex.asOrderHom x.val a else i) = i
      by_cases ht : stdSimplex.asOrderHom t a = 0
      · rw [ite_eq_left ht]
        by_cases h : stdSimplex.asOrderHom x.val a ≤ i
        · exact Or.inl (min_eq_left h)
        · exact Or.inr (min_eq_right (le_of_not_ge h))
      · rw [ite_eq_right ht]
        cases b <;> simp
    exact hval.elim (fun h => Or.inl ⟨a, h.symm⟩) Or.inr
  · exact Or.inr hj

/-- 概要：min(-,i) から恒等または定値へ向かうホーン内の円柱。
方針：各単体の単調写像を区間の値で切り替える。
規約：true は恒等、false は頂点 i。全単体でホーンに留まる。
使われ方：二つの単体的ホモトピーの共通のデータ。 -/
def hornContractionPrism (b : Bool) :
    (horn (n + 1) i : SSet.{u}) ⊗ Δ[1] ⟶ (horn (n + 1) i : SSet.{u}) where
  app m := ↾fun x => ⟨stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrismOrder n i b x.1 x.2)), _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrism_mem n i b x.1 x.2⟩
  naturality := by
    intro m k f
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext a
    rfl

/-- 概要：ホーンの min(-,i) 自己写像。
方針：円柱の零端点を取る。規約：頂点 i を固定。
使われ方：恒等と定値を結ぶ二つのホモトピーの共通始点。 -/
def hornContractionMin : (horn (n + 1) i : SSet.{u}) ⟶ horn (n + 1) i :=
  SSet.ι₀ ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i true

/-- 概要：ホーン内の頂点 i。
方針：零単体の単調定値写像を取る。規約：次元は n+1≥1。
使われ方：収縮の切断。 -/
def hornContractionVertex : (horn (n + 1) i : SSet.{u}) _⦋0⦌ := by
  refine ⟨stdSimplex.objEquiv.symm (SimplexCategory.const _ _ i), ?_⟩
  change Set.range (fun _ : Fin 1 => i) ∪ {i} ≠ Set.univ
  intro he
  obtain ⟨j, hj⟩ := exists_ne i
  have h := Set.eq_univ_iff_forall.mp he j
  rcases h with ⟨a, ha⟩ | h
  · exact hj ha.symm
  · exact hj h

/-- 概要：零単体から頂点 i への切断。
方針：頂点による定値写像。規約：元のホーンに値を持つ。
使われ方：正規化収縮の逆射。 -/
def hornContractionSection : (Δ[0] : SSet.{u}) ⟶ horn (n + 1) i :=
  SSet.const (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionVertex n i)

/-- 概要：ホーンから零単体への射。
方針：零単体の唯一の頂点への定値写像。規約：同じ宇宙。
使われ方：正規化収縮の順射。 -/
def hornContractionProjection : (horn (n + 1) i : SSet.{u}) ⟶ Δ[0] :=
  SSet.const (stdSimplex.obj₀Equiv.symm 0)

/-- 概要：円柱の始端は共通の min 写像。
方針：各単体で計算する。規約：両円柱に共通。使われ方：ホモトピーの始端。 -/
lemma hornPrism_zero (b : Bool) :
    SSet.ι₀ ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i b = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionMin n i := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  rfl

/-- 概要：true 円柱の終端は恒等。
方針：各単体で計算する。規約：全単体の等式。使われ方：ホモトピーの終端。 -/
lemma hornPrism_one_id : SSet.ι₁ ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i true = 𝟙 _ := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  rfl

/-- 概要：false 円柱の終端は頂点 i への定値写像。
方針：各単体で計算する。規約：元の切断と射影。使われ方：収縮の終端。 -/
lemma hornPrism_one_const : SSet.ι₁ ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i false =
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionProjection n i ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionSection n i := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  rfl

/-- 概要：min 自己写像から恒等への単体的ホモトピー。
方針：true の円柱を使う。規約：モデル構造の仮定なし。
使われ方：正規化鎖の収縮ホモトピー。 -/
def hornContractionToId :
    SSet.Homotopy (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionMin n i) (𝟙 (horn (n + 1) i : SSet.{u})) where
  h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i true
  h₀ := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrism_zero n i true
  h₁ := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrism_one_id n i
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：min 自己写像から頂点への定値写像への単体的ホモトピー。
方針：false の円柱を使う。規約：同じ共通始点を保持。
使われ方：恒等から定値への鎖ホモトピーの構成。 -/
def hornContractionToConst : SSet.Homotopy (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionMin n i)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionProjection n i ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionSection n i) where
  h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionPrism n i false
  h₀ := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrism_zero n i false
  h₁ := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornPrism_one_const n i
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.SimplicialChains.AlexanderWhitney
