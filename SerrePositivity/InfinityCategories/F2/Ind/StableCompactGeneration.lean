module

public import SerrePositivity.InfinityCategories.F2.Ind.Stability
public import SerrePositivity.InfinityCategories.F2.Ind.CompactGeneratorImage

/-!
概要：安定 Ind の compact 生成と元の完全 Yoneda を一つの公開界面にまとめる。
方針：保存済みの安定性・生成同値・同じ頂点の filtered 表示をそのまま組み合わせる。
規約：交換入力と C の有限全存在を明示し、同値の順射を元の compact Yoneda に固定。
使われ方：I-2 c・e の結論、および K-B の K-7 d4 向け入力。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 安定性・完全包含・実生成同値と、任意の元の頂点の compact 生成表示。 -/
structure StableCompactGeneration (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] where
  /-- 元の Ind 自身の安定性。 -/
  stable : IsStable (IndInfinity κ C)
  /-- 元の全 Yoneda の充満忠実性。 -/
  fullyFaithful : IsFullyFaithful (indYoneda κ C)
  /-- 同じ Yoneda の完全性。 -/
  exactYoneda : IsExactFunctor (indYoneda κ C)
  /-- 同じ Yoneda 像の κ-compact 性。 -/
  yonedaCompact : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ
    ((indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x))
  /-- 元の C と compact 部分との実同値。 -/
  equivalence : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C)
    (Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C))
  /-- 選択した同値の順射を元の compact Yoneda に固定する。 -/
  equivalence_hom : equivalence.hom = Compact.compactIndYoneda κ C
  /-- 任意の元の頂点そのものを頂点とする、小さい filtered 生成表示。 -/
  generated : ∀ x : (IndInfinity κ C) _⦋0⦌,
    ∃ (I : SSet.{u}) (hI : Quasicategory I),
      letI := hI
      IsKappaFiltered κ I ∧ ∃ a : I ⟶ C,
        ∃ c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ equivalence.hom ≫
          Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)),
          c.vertex = x ∧ IsColimitCone c

/-- 明示交換入力のもとで、安定な冪等完備 C の安定 compact 生成界面を構成。 -/
def ind_stableCompactGeneration (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    (hC : Idempotent.IsIdempotentComplete C) : StableCompactGeneration κ C where
  stable := ind_isStable κ hκ hex C
  fullyFaithful := indYoneda_isFullyFaithful κ C
  exactYoneda := indYoneda_isExactFunctor κ hκ hex C
  yonedaCompact := Compact.indYoneda_isKappaCompact κ
  equivalence := compactGenerationEquivalence κ hC
  equivalence_hom := compactGenerationEquivalence_hom κ hC
  generated := indVertex_has_compactGeneratorPresentation κ hC

/-- 公開界面の選んだ逆射は、元の全 compact 包含を回収する。 -/
def StableCompactGeneration.inverse_inclusion {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C] (g : StableCompactGeneration κ C) :
    FunctorIso (g.equivalence.inv ≫ indYoneda κ C)
      (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)) :=
  compactGenerationChoice_inclusion κ g.equivalence g.equivalence_hom

end SerrePositivity.InfinityCategories.F2.Ind
