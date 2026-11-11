module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocallySmallHomTypes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CompactGenerators

/-!
概要：小さい compact 生成族の全 retract を、局所小ささを用いて小さい族で代表する。
方針：生成対象の小さい自己射型で分裂する冪等射を符号化し、同じ冪等射の分裂の一意同型を使う。
規約：元の対象の retract 表示を用い、coherent な分裂の追加存在を仮定しない。
使われ方：引き戻しの両成分の全 compact 対象を小さい候補族で扱う。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall C)
  {T : Type u} (v : T → C _⦋0⦌)

/-- 概要：小さい族の対象の分裂する自己射の小さい符号型。
方針：局所小ささで自己射型を縮小し、元の頂点での分裂の存在を付ける。
規約：分裂の存在だけを符号に付け、全空間の対象を添字にしない。
使われ方：retract 閉包の小さい代表族。 -/
def SmallRetractIndex : Type u := by
  have (t : T) : Small.{u} (HomotopyCategory.mk (v t) ⟶ HomotopyCategory.mk (v t)) :=
    hC.hom_small _ _
  exact Σ t : T, {f : Shrink.{u} (HomotopyCategory.mk (v t) ⟶ HomotopyCategory.mk (v t)) //
    ∃ x : C _⦋0⦌, ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x (v t),
      s.r ≫ s.i = (equivShrink _).symm f}

/-- 概要：小さい符号から元の生成対象の自己射を回収する。
方針：指定された縮小の逆を使う。
規約：ホモトピー圏内の元の自己射。
使われ方：二つの retract の冪等射の照合。 -/
def smallRetractEndomorphism (t : SmallRetractIndex hC v) :
    HomotopyCategory.mk (v t.1) ⟶ HomotopyCategory.mk (v t.1) := by
  have (t : T) : Small.{u} (HomotopyCategory.mk (v t) ⟶ HomotopyCategory.mk (v t)) :=
    hC.hom_small _ _
  exact (equivShrink _).symm t.2.1

/-- 概要：各分裂符号に対して元の圏内の retract の頂点を一つ選ぶ。
方針：符号に記録した元の分裂の存在から頂点を取る。
規約：小さい符号型で添字付ける。
使われ方：小さい retract 代表族。 -/
def smallRetractFamily (t : SmallRetractIndex hC v) : C _⦋0⦌ := t.2.2.choose

/-- 概要：選んだ元の頂点は指定生成対象の retract。
方針：符号の同じ分裂の存在から全 retract データを回収する。
規約：同じ元の二頂点間の射を保持する。
使われ方：代表族の compact 性。 -/
def smallRetractFamilyRetraction (t : SmallRetractIndex hC v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (smallRetractFamily hC v t) (v t.1) :=
  t.2.2.choose_spec.choose

/-- 概要：選んだ retract の冪等射は元の符号の自己射。
方針：記録された分裂の指定等式を回収する。
規約：自己射の厳密な等式。
使われ方：元の全 retract と選んだ代表との頂点同型。 -/
lemma smallRetractFamilyRetraction_endomorphism (t : SmallRetractIndex hC v) :
    (smallRetractFamilyRetraction hC v t).r ≫ (smallRetractFamilyRetraction hC v t).i =
      smallRetractEndomorphism hC v t := t.2.2.choose_spec.choose_spec

/-- 概要：元の小さい族の任意の retract は小さい代表族の一つと頂点同型。
方針：元の retract の冪等射を符号化し、同じ冪等射の二つの分裂を比較する。
規約：元の retract の射を使い、分裂の存在を追加しない。
使われ方：全 compact 対象の小さい代表族への回収。 -/
lemma exists_smallRetractFamily_iso (a : T) (x : C _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x (v a)) :
    ∃ t : SmallRetractIndex hC v, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (smallRetractFamily hC v t)) := by
  have (t : T) : Small.{u} (HomotopyCategory.mk (v t) ⟶ HomotopyCategory.mk (v t)) :=
    hC.hom_small _ _
  let s := hx.some
  let t : SmallRetractIndex hC v := ⟨a, ⟨equivShrink _ (s.r ≫ s.i),
    x, s, (Equiv.symm_apply_apply _ _).symm⟩⟩
  refine ⟨t, ⟨s.isoOfSameIdempotent (smallRetractFamilyRetraction hC v t) ?_⟩⟩
  rw [smallRetractFamilyRetraction_endomorphism]
  exact (Equiv.symm_apply_apply _ _).symm

/-- 概要：元の小さい族が κ-compact なら全 retract 代表族も κ-compact。
方針：選んだ元の retract に compact 性の retract 閉性を適用する。
規約：元の全 Hom による compact 性を保つ。
使われ方：全 compact 対象を代表する族の compact 性。 -/
lemma smallRetractFamily_isKappaCompact {κ : Cardinal.{u}}
    (hv : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (v t))
    (t : SmallRetractIndex hC v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (smallRetractFamily hC v t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract ⟨smallRetractFamilyRetraction hC v t⟩ (hv t.1)

include hC in
/-- 概要：小さい compact 生成圏を持つ局所的に小さい圏の全 compact 対象は、小さい族で代表される。
方針：任意の compact 対象を生成対象の retract とし、その分裂を小さい符号に回収する。
規約：元の対象との頂点同型を全データで供給する。
使われ方：引き戻しの両成分の全 compact 対象を小さい候補族に含める。 -/
lemma exists_smallCompactFamily {κ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i) :
    ∃ (T : Type u) (v : T → C _⦋0⦌),
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (v t)) ∧
      ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x →
        ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t)) := by
  let w : A _⦋0⦌ → C _⦋0⦌ := fun a ↦ i.app _ (ULift.up a)
  refine ⟨SmallRetractIndex hC w, smallRetractFamily hC w,
    smallRetractFamily_isKappaCompact hC w hi.compact, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hi.retract_generator hx
  exact exists_smallRetractFamily_iso hC w a x ha

/-- 概要：元の κ-accessible 圏の全 κ-compact 対象は小さい族で代表される。
方針：元の生成圏と局所小ささを accessibility から回収する。
規約：厳密な固定頂点写像の小ささは要求しない。
使われ方：一般の accessible 圏での引き戻し候補の小さい添字。 -/
lemma IsKappaAccessible.exists_smallCompactFamily {κ : Cardinal.{u}}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (T : Type u) (v : T → C _⦋0⦌),
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (v t)) ∧
      ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x →
        ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t)) := by
  obtain ⟨A, hA, i, hi⟩ := h.2.2
  have := hA
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallCompactFamily
    h.isAccessible.isLocallySmall i hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_smallCompactFamily)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
