module

public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：trivial Kan fibration から明示的な quasicategory の同値を構成する。
方針：切断を選び、内部 Hom の可縮な fiber で単位の可逆二胞体を作る。
規約：モデル構造や弱同値は用いない。
使われ方：Kerodon Proposition 4.5.4.11、Theorem 4.8.4.1。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：内部 Hom による後合成は trivial Kan fibration 性を保つ。
方針：閉構造の随伴で境界の持ち上げを積の境界の持ち上げへ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.5.4.11 の切断の空間。 -/
instance trivialKanFibration_ihom_map {E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration p] (A : SSet.{u}) : TrivialKanFibration ((ihom A).map p) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofIsInitialLeft (curriedTensor SSet.{u})
    (initial.to A) (boundary n).ι initialIsInitial
  let sq' := Functor.PullbackObjObj.ofIsInitial internalHom (initial.to A) p initialIsInitial
  change HasLiftingProperty (boundary n).ι sq'.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  change HasLiftingProperty (A ◁ (boundary n).ι) p
  have hm : Mono (A ◁ (boundary n).ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [mono_iff_injective]
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    change (a, b.val) = (a', b'.val) at h
    exact Prod.ext
      (congrArg (fun z : A.obj d × (Δ[n] : SSet.{u}).obj d ↦ z.1) h)
      (Subtype.ext (congrArg (fun z : A.obj d × (Δ[n] : SSet.{u}).obj d ↦ z.2) h))
  exact TrivialKanFibration.mem (p := p) _ hm

/-- 概要：trivial Kan fibration には厳密な切断が存在する。
方針：空部分複体から標的への単射に対して持ち上げる。
規約：切断との合成は標的の恒等射。
使われ方：Kerodon Proposition 4.5.4.11 の同値の逆射。 -/
lemma trivialKanFibration_exists_section {E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration p] : ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  have := TrivialKanFibration.mem (p := p) (⊥ : B.Subcomplex).ι inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to E) (⊥ : B.Subcomplex).ι p (𝟙 B) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 概要：quasicategory 間の trivial Kan fibration は A3a の明示的な同値。
方針：切断を逆射とし、内部 Hom の可縮な fiber で単位の可逆二胞体を作る。
規約：順方向の射は与えられた p そのもの。
使われ方：Kerodon Proposition 4.5.4.11、Theorem 4.8.4.1。 -/
@[kerodon 01EH]
noncomputable def qCatEquivalenceOfTrivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    QCatEquivalence E B := by
  let s := Classical.choose (trivialKanFibration_exists_section p)
  have hs : s ≫ p = 𝟙 B := Classical.choose_spec (trivialKanFibration_exists_section p)
  let q := (ihom E).map p
  let b := functorVertex p
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex (p ≫ s), by
    rw [pinchedConstant_zero]
    change functorVertex ((p ≫ s) ≫ p) = functorVertex p
    rw [Category.assoc, hs, Category.comp_id]⟩
  let v₁ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex (𝟙 E), by
    rw [pinchedConstant_zero]
    change functorVertex ((𝟙 E) ≫ p) = functorVertex p
    rw [Category.id_comp]⟩
  let hi := terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  refine { hom := p
           inv := s
           homInvIso := VertexIso.map hi (vertexFiberι q b)
           invHomIso := ?_ }
  exact eqToIso (congrArg (fun f : B ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex f)) hs)

/-- 概要：quasicategory 間の trivial Kan fibration は同値という性質を持つ。
方針：明示的な同値のデータを存在量化する。
規約：射 p を固定した同値性。
使われ方：Kerodon Theorem 4.8.4.1 のファイブレーションへの還元。 -/
@[kerodon 01EH, kerodon 04FA]
lemma isQCatEquivalence_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    IsQCatEquivalence p := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence

end SerrePositivity.InfinityCategories
