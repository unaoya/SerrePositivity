module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitEndInitiality
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanHomEnd

/-!
概要：既知の普遍 span の全 Hom の族を共通 path end へ移し、元の余錐との比較の正確な標的にする。
方針：native な span の余極限性を strict 表示へ移し、既存の二つの end 比較の同値を合成する。
規約：元の余錐の族とのホモトピーは未証明の入力として明示。使われ方：残る経路の整合性の検証箇所。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)

/-- 既知の普遍 span の全 Hom の族から、元の図式側と同じ共通 path end への実際の射。 -/
def nativeSpanUniversalFamilyToPathEnd :
    pinchedHomLeft (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex y ⟶
      partialColimitHomPathEnd hp p y c hc dB dC :=
  coconePointHomFamily (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) y ≫
    partialColimitSpanCoconeToHomEnd hp p c hc dB dC y ≫
    partialColimitHomEndToPathEnd hp p y c hc dB dC

/-- 普遍 span 側の全 Hom の族の共通 path end への比較は、無条件にホモトピー同値。 -/
lemma nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (nativeSpanUniversalFamilyToPathEnd hp p c hc dB dC y) := by
  have ht : IsColimitCone (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) :=
    (coherentCoconeOfDiagramEq_isColimit_iff (strictCoherentDiagram_eq_kanDiagram _).symm _).mp
      (partialColimitPushoutCocone_isColimit c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
  have : KanComplex (weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
      (partialColimitHomCospan hp p y c hc dB dC)) := bousfieldKanWeightedSections_kanComplex _
  exact (coconePointHomFamily_homotopyEquivalence _ ht y).comp
    ((partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y).comp
      (partialColimitHomEndToPathEnd_homotopyEquivalence hp p y c hc dB dC))

variable [Mono g]

/-- 指定経路で構成した余錐の頂点は、同じ strict な普遍 span の頂点そのもの。 -/
lemma specifiedPathCocone_vertex_eq_strictSpan :
    (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex =
      (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex :=
  (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)).property.trans
    (pinchedConstant_zero _)

/-- 同じ実際の頂点の左 Hom で表示した、比較先の普遍 span の共通 path end への族。 -/
def specifiedCoconeNativeFamilyToPathEnd :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      partialColimitHomPathEnd hp p y c hc dB dC :=
  eqToHom (congrArg (fun v ↦ pinchedHomLeft v y)
      (specifiedPathCocone_vertex_eq_strictSpan hp p c hc dB dC)) ≫
    nativeSpanUniversalFamilyToPathEnd hp p c hc dB dC y

/-- 頂点の表示を揃えた比較先も、共通 path end への実際のホモトピー同値。 -/
lemma specifiedCoconeNativeFamilyToPathEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y) :=
  (homotopyEquivalence_of_isIso _).comp
    (nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence hp p c hc dB dC y)

/-- 残る全パラメータの族のホモトピーが得られれば、構成した元の余錐の余極限性を結論できる。 -/
lemma specifiedPathCocone_isColimit_of_pathFamily_homotopy
    (hB : IsColimitCone dB) (hC : IsColimitCone dC)
    (h : ∀ y : SpaceInfinity.{u} _⦋0⦌, Nonempty (SSet.Homotopy
      (partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) y)
      (specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y))) :
    IsColimitCone (partialColimitSpecifiedPathCocone hp p c hc dB dC) := by
  apply (isColimitCone_iff_partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC _).mpr
  intro z
  obtain ⟨H⟩ := h z
  have hh := specifiedCoconeNativeFamilyToPathEnd_homotopyEquivalence hp p c hc dB dC z
  have he := hh.isQCatEquivalence
  exact (he.ofFunctorIso (functorIsoOfSimplicialHomotopy H).symm).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
