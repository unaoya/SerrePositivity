module

public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-!
概要：全ホーンの持ち上げ性と Mathlib の Fibration クラスの接続。
方針：既存クラスをホーンの rlp としてだけ使い、内部 Hom の持ち上げを利用する。
規約：Kan–Quillen モデル構造や弱同値は用いない。
使われ方：HTT §2.2、Kerodon §4.8.4 の可縮な写像空間の fiber。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全ホーンの持ち上げ性を既存の Fibration クラスへ移す。
方針：クラスの定義であるホーンの rlp を展開する。
規約：モデル構造の公理は使わない。
使われ方：HTT §2.2 の内部 Hom のパラメーター付き持ち上げ。 -/
lemma fibration_of_hasLiftingProperty_horn {X Y : SSet.{u}} (q : X ⟶ Y)
    (h : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty (horn (n + 1) i).ι q) :
    Fibration q := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  exact h n i

/-- 概要：既存の Fibration は左ファイブレーション。
方針：全ホーンの rlp を左ホーンに制限する。
規約：単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.4.2 の辺の持ち上げ。 -/
instance fibration_leftFibration {X Y : SSet.{u}} (q : X ⟶ Y) [Fibration q] :
    LeftFibration q where
  mem := by
    have h := (SSet.modelCategoryQuillen.fibration_iff q).mp inferInstance
    intro A B j hj
    cases hj with
    | @intro n i hi => exact h _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ i)

/-- 概要：Kan 複体間の右ファイブレーションを既存の Fibration クラスへ移す。
方針：全ホーンの相対充填をクラスの定義へ戻す。
規約：モデル構造の弱同値や因子分解は使わない。
使われ方：HTT §2.2、Kerodon §4.8.4 の写像空間の射。 -/
instance rightFibration_fibration_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [RightFibration q] : Fibration q :=
  fibration_of_hasLiftingProperty_horn q (rightFibration_hasLiftingProperty_horn_of_kanComplex q)

/-- 概要：quasicategory の同値である Fibration には厳密な切断がある。
方針：内部 Hom の持ち上げで逆射を余単位の可逆な辺に沿って恒等射の上へ移す。
規約：切断と元の射の合成は厳密に恒等射。
使われ方：HTT §2.2、Kerodon §4.8.4 のホモトピー逆の相対化。 -/
lemma fibration_exists_section_of_isQCatEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) : ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  let e := he.choose
  let g := e.inv
  let β := FunctorIso.edge e.invHomIso
  let q := (ihom B).map p
  obtain ⟨F, hF₀, hFq⟩ := leftFibration_liftEdge_source q (functorVertex g) β
  let v := ((ihom B).obj E).δ 0 (SSet.yonedaEquiv F)
  let s := (functorVertexEquiv B E).symm v
  have hs : functorVertex s = v := (functorVertexEquiv B E).apply_symm_apply v
  refine ⟨s, functorVertex_injective ?_⟩
  change q.app (Opposite.op ⦋0⦌) (functorVertex s) = functorVertex (𝟙 B)
  rw [hs]
  calc
    _ = ((ihom B).obj B).δ 0 (q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F)) :=
      ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op) (SSet.yonedaEquiv F)
    _ = ((ihom B).obj B).δ 0 β.edge := by
      rw [← SSet.yonedaEquiv_comp, hFq]
      exact congrArg (fun v ↦ ((ihom B).obj B).δ 0 v)
        ((SSet.yonedaEquiv (X := (ihom B).obj B) (n := ⦋1⦌)).apply_symm_apply β.edge)
    _ = functorVertex (𝟙 B) := β.tgt_eq

/-- 概要：同値の厳密な切断の逆合成は始域の恒等関手と同型。
方針：元の単位を切断で前合成し、切断の厳密な等式で簡約する。
規約：同型は関手単体集合のホモトピー圏で取る。
使われ方：HTT §2.2 の切断から fiber 内の収縮への移行。 -/
lemma IsQCatEquivalence.functorIsoOfSection {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {p : E ⟶ B} (he : IsQCatEquivalence p)
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) : Nonempty (FunctorIso (p ≫ s) (𝟙 E)) := by
  let e := he.choose
  have t := FunctorIso.precomp e.homInvIso (p ≫ s)
  change FunctorIso ((p ≫ s) ≫ (p ≫ e.inv)) ((p ≫ s) ≫ 𝟙 E) at t
  have ht : (p ≫ s) ≫ (p ≫ e.inv) = p ≫ e.inv := by
    rw [Category.assoc, ← Category.assoc s p e.inv, hs, Category.id_comp]
  rw [ht, Category.comp_id] at t
  exact ⟨t.symm ≪≫ e.homInvIso⟩

end SerrePositivity.InfinityCategories
