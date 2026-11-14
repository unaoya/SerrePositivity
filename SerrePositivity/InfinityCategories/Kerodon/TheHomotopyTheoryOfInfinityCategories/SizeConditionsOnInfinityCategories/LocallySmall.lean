module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.PinchedHom

/-!
概要：accessible ∞ 圏の各写像空間に小さい Kan 模型を供給する。
方針：固定頂点の小ささから二対象の小さい全部分模型を作り、Ind 同値で一般へ移す。
規約：局所小ささは写像空間の全同値で述べ、ホモトピー圏の Hom 集合だけに弱めない。
使われ方：前層・Ind・presentable ∞ 圏の局所小ささの公開界面。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：任意の二対象の写像空間が、同じ宇宙 u の Kan 空間の持ち上げと全同値を持つこと。
方針：元の pinched Hom との明示的な全 ∞ 圏同値を量化する。
規約：対象の型自体の小ささは要求しない。
使われ方：accessible 圏と presentable 圏の局所小ささ。 -/
def IsLocallySmall (C : SSet.{u + 1}) [Quasicategory C] : Prop :=
  ∀ x y : C _⦋0⦌, ∃ (K : SSet.{u}) (hK : KanComplex K),
    letI := hK
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y))

/-- 概要：固定頂点の全写像が小さい ∞ 圏は局所小さい。
方針：二対象の張る全部分圏を縮小し、その充満忠実性で元の写像空間を回収する。
規約：元の二対象を厳密に回収し、実際の全写像空間を比較する。
使われ方：前層と Ind の局所小ささ。 -/
lemma isLocallySmall_of_smallFixedVertexMaps {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps C) : IsLocallySmall C := by
  intro x y
  let v : ULift.{u} (Fin 2) → C _⦋0⦌ := fun k ↦ ![x, y] k.down
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C (fun z ↦ z ∈ Set.range v)
  let sx : S.toSSet _⦋0⦌ := ⟨x, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, Functor.map_id_apply]
    exact ⟨ULift.up 0, rfl⟩⟩
  let sy : S.toSSet _⦋0⦌ := ⟨y, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, Functor.map_id_apply]
    exact ⟨ULift.up 1, rfl⟩⟩
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelIso hC v
  let a := e.inv.app (Opposite.op ⦋0⦌) sx
  let b := e.inv.app (Opposite.op ⦋0⦌) sy
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hC v
  have hx : f.app (Opposite.op ⦋0⦌) a = x := by
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) sx)
  have hy : f.app (Opposite.op ⦋0⦌) b = y := by
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) sy)
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a.down b.down
  have hK : KanComplex K := inferInstance
  have he := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso.{u, u + 1} a.down b.down)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isFullyFaithful hC v a b).isQCatEquivalence.choose))
  refine ⟨K, hK, ?_⟩
  have hh : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (f.app (Opposite.op ⦋0⦌) a) (f.app (Opposite.op ⦋0⦌) b))) := ⟨he⟩
  simpa only [hx, hy] using hh

/-- 概要：充満忠実関手の標的が局所小さいなら始域も局所小さい。
方針：標的の小さい Kan 模型と、元の pinched Hom 作用の逆同値を合成する。
規約：充満忠実性は全写像空間について要求する。
使われ方：Ind 表現からの accessible 圏の局所小ささ。 -/
lemma IsLocallySmall.of_fullyFaithful {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (hE : IsLocallySmall E)
    (F : C ⟶ E) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F) : IsLocallySmall C := by
  intro x y
  obtain ⟨K, hK, ⟨e⟩⟩ := hE (F.app _ x) (F.app _ y)
  exact ⟨K, hK, ⟨e.trans (hF x y).isQCatEquivalence.choose.symm⟩⟩

/-- 概要：任意の小さい ∞ 圏の Indκ は局所小さい。
方針：元の Ind の固定頂点写像の小ささを二対象模型の構成に渡す。
規約：κ の正則性や全小余極限の存在を追加しない。
使われ方：accessible 圏の局所小ささ。 -/
lemma indInfinity_isLocallySmall (κ : Cardinal.{u}) (A : SSet.{u}) [Quasicategory A] :
    IsLocallySmall (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) :=
  isLocallySmall_of_smallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ A)

/-- 概要：accessible ∞ 圏は局所小さい。
方針：実際に構成した小さい Ind 模型への全同値で写像空間を戻す。
規約：局所小ささを accessibility の定義の入力にしない。
使われ方：presentable ∞ 圏の局所小ささ。 -/
lemma IsAccessible.isLocallySmall {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) : IsLocallySmall C := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hA
  exact (indInfinity_isLocallySmall κ A).of_fullyFaithful e.inv
    e.symm.isQCatEquivalence.isFullyFaithful

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsAccessible (isLocallySmall)


/-- 概要：presentable ∞ 圏は局所小さい。
方針：同じ accessibility から小さい全写像空間の模型を得る。
規約：元の定義に局所小ささを追加仮定しない。
使われ方：随伴関手定理の小さい解集合の準備。 -/
lemma IsPresentable.isLocallySmall {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) : IsLocallySmall C := hC.isAccessible.isLocallySmall

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable (isLocallySmall)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.4.2" (partial := component) "仮定：準圏（Lean が弱い：安定性は不要）。結論：presentable なら局所小で、余完備な Ind 模型による presentable 性の判定（Lean が弱い：小余積・hC の局所小性・単一の κ コンパクト生成対象という三条件の判定を与えない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall
attribute [cite HTT "5.4.1.7" (partial := component) "仮定：準圏 C（HTT と一致）。結論：(1) 各二対象間の全 Hom が小 Kan 模型を持つ条件を局所小性と定義する（一致）。(2) 任意の小対象族が張る全部分準圏の本質的小性との一般の iff は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall
attribute [cite HTT "5.4.1.8" (partial := component) "仮定：小準圏 D（HTT と一致）。結論：P(D) の局所小性（原典の最終文と一致）。一般の C,D についての冒頭の「CD is essentially small」は C=Set,D=Δ⁰ で成り立たず、証明末尾は locally small を述べる（source-notes 参照）。この候補はその冒頭の誤記を正しいとするものではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall
attribute [cite HTT "5.4.2.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsAccessible.isLocallySmall
