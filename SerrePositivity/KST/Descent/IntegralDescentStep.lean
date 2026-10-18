module

public import SerrePositivity.KST.Descent.OrbitDescentStep
public import SerrePositivity.KST.Descent.OrbitCenterInduction
public import SerrePositivity.KST.Descent.BasicDescent
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# 整な基底における次元帰納の一段

## 概要
厳密に小さい次元の切断を持つ射への帰納仮定から、整な基底上の指定降下を導く。

## 方針
元の切断の相異なる移動を用い、一致中心で次元を下げ、実際の軌道段階を適用する。

## 規約
自然な blowup 列と有限積保存は実降下から供給すべき条件。
低次元の帰納仮定は最小公理へ追加せず、厳密に小さい次元に限る。

## 使われ方
論文 定理 3.1 の「整 → 被約 → 一般」の整な場合。
τ 位相の層論を Čech 計算に置き換える全体経路の、切断を持つ射の帰納段階。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：厳密に小さい基底次元に対する切断を持つ射の帰納仮定（論文 定理 3.1）。
方針：同じ有限型の圏内の幾何射と指定作用・切断・点の推移性を量化する。
規約：これは帰納法の仮定の型であり、前層の公理ではない。
使われ方：整な基底の一致中心に、局所降下を供給する。 -/
def SectionedDescentBelow {S : Scheme.{u}} {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    (G : Type u) [Group G] (d : ℕ) : Prop :=
  ∀ (B V : FiniteTypeSchemes S) [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V), s ≫ p = 𝟙 B →
    (∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y) →
    topologicalKrullDim B.obj.left < d → L.PiDescent p action over_base

/-- 概要：零より低い次元への帰納仮定は空の基底の場合から得られる（論文 定理 3.1）。
方針：点が存在すればその閉包が既約閉集合となり次元が非負になることを使う。
規約：空の基底の次元は ⊥ とし、零次元へ丸めない。
使われ方：自然数の次元上界に関する強い帰納の始点。 -/
theorem sectionedDescentBelow_zero {S : Scheme.{u}} {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    (G : Type u) [Group G] : SectionedDescentBelow L G 0 := by
  intro B V _ p action over_base _ _ _ bound
  let : IsEmpty B.obj.left := ⟨fun x ↦ by
    have : Nonempty (IrreducibleCloseds B.obj.left) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have nonnegative : 0 ≤ topologicalKrullDim B.obj.left := Order.krullDim_nonneg
    have negative : topologicalKrullDim B.obj.left < 0 := by simpa using bound
    exact (not_lt_of_ge nonnegative) negative⟩
  exact L.piDescent_of_empty_target p action over_base

/-- 概要：整な基底の帰納段階を実際の低次元の中心上の降下で閉じる（論文 定理 3.1）。
方針：相異なる移動切断の被覆・一致中心の次元低下・中心の切断と推移性を構成する。
規約：中心上の降下を独立した仮定にせず、低次元に限る帰納仮定から供給する。
使われ方：全体の次元帰納における整な基底の一段。 -/
theorem NaturalBlowupSequences.integral_reducedSource_piDescent_of_below {S : Scheme.{u}}
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [∀ H n, PreservesFiniteProducts (L H n)]
    {G : Type u} [Group G] [Finite G] {B V : FiniteTypeSchemes S}
    [IsIntegral B.obj.left] [IsReduced V.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V)
    (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d) : L.PiDescent p action over_base := by
  classical
  have : IsSeparated p.hom.left := by
    have : IsSeparated (p.hom.left ≫ B.obj.hom) := by rw [p.hom.w]; infer_instance
    exact IsSeparated.of_comp p.hom.left B.obj.hom
  let I := TranslatedSectionIndex action s
  let sections : I → (B ⟶ V) := fun t ↦ t.val
  let Z := coincidenceClosedSet (fun t : I ↦ (sections t).hom)
  let C := closedCenterPullback p Z
  let centerBase := reducedClosedAsFiniteType B Z
  let centerMap : C ⟶ centerBase := closedCenterPullbackSecond p Z
  let centerAction := orbitCenterAction p sections action over_base
  let centerInvariant := orbitCenterProjection_invariant p sections action over_base
  have : IsSeparated C.obj.hom :=
    inferInstanceAs (IsSeparated
      (pullback.fst p.hom.left (reducedClosedInclusion Z) ≫ V.obj.hom))
  have center_dimension : topologicalKrullDim centerBase.obj.left < d :=
    translatedSection_center_dimension_lt_bound action s d bound
  have center_descent : L.PiDescent centerMap centerAction centerInvariant :=
    below centerBase C centerMap centerAction centerInvariant (orbitCenterSection p sections s hs)
      (orbitCenterSection_identity p sections s hs)
      (orbitCenterAction_transitive_on_fibers p sections action over_base transitive)
      center_dimension
  exact data.orbit_piDescent_of_center p sections
    (translatedSection_identity p s hs action over_base)
    (translatedSection_covering p s hs action transitive) action over_base
    (translatedSection_equivariant action s) center_descent

/-- 概要：整な基底で始域の被約性を要求せずに低次元から降下する（論文 定理 3.1）。
方針：切断を始域の被約化へ持ち上げ、被約な場合を証明して公理 (3) で戻す。
規約：Noether な基底 S と L の冪零不変性を明示する。
使われ方：全体の次元帰納における整な基底の一般の始域に対する段階。 -/
theorem NaturalBlowupSequences.integral_piDescent_of_below {S : Scheme.{u}}
    [IsNoetherian S] {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)]
    {G : Type u} [Group G] [Finite G] {B V : FiniteTypeSchemes S}
    [IsIntegral B.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V)
    (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d) : L.PiDescent p action over_base := by
  have : IsSeparated (finiteTypeReduction V).obj.hom :=
    inferInstanceAs (IsSeparated (schemeReductionInclusion V.obj.left ≫ V.obj.hom))
  apply (Nilinvariant.piDescent_iff_reducedSource L p action over_base).mpr
  apply data.integral_reducedSource_piDescent_of_below
    (finiteTypeReductionInclusion V ≫ p) (finiteTypeReductionAction action)
    (reducedSourceAction_over_base p action over_base) (finiteTypeReductionLift s)
    _ (reducedSourceAction_transitive_on_fibers p action transitive) d bound below
  exact (finiteTypeReductionLift_comp_inclusion_assoc s p).trans hs

end SerrePositivity.KST.Descent
