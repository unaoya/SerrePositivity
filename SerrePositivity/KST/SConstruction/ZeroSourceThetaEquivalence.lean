module
public import SerrePositivity.KST.SConstruction.ZeroSourceRightEquivalence
public import SerrePositivity.KST.SConstruction.VariableTimeEquivalence

/-! # θ の可逆性と可変時刻での gapped 性
概要：大域的な θ は点ごとに可逆であり、可変時刻の評価で gapped 性を保つ。
方針：指定右辺の可逆性を二つの自明ファイブレーションで反映する。
規約：零 subobject の入力空間自体の安定性を要求しない。使われ方：左 fiber 内の θ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：固定始点の入力矢印の θ は各頂点で可逆。
方針：終点射影で元の右辺に写ることと充満忠実性による反映。
規約：指定した持ち上げの辺そのものに対する判定。使われ方：cofiber 図式への反映。 -/
lemma zeroSourceThetaInput_isInvertible {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C)
    (b : (zeroSourceCofibers z) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((zeroSourceThetaInput z).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1))) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fixedSourceArrowsTarget z.vertex) :=
    fixedSourceArrowsTarget_trivialKanFibration z.vertex z.isInitial
  let : Quasicategory (fixedSourceArrows z.vertex) :=
    quasicategory_of_innerFibration (fixedSourceArrowsTarget z.vertex)
  let s : ((Δ[1] : SSet.{u}) ⊗ zeroSourceCofibers z) _⦋1⦌ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (zeroSourceThetaInput_target z)
    (Opposite.op ⦋1⦌)) s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (fixedSourceArrowsTarget z.vertex)).reflects_isInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((zeroSourceThetaInput z).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 (zeroSourceCofibersRightPrism_isInvertible z b)

/-- 概要：cofiber 図式の θ は各頂点で可逆。
方針：入力矢印での可逆性を cofiber 射影の充満忠実性で反映する。
規約：比較の選択の可逆性を仮定しない。使われ方：可変時刻での gapped 性。 -/
lemma zeroSourceTheta_isInvertible {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (b : (zeroSourceCofibers z) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((zeroSourceTheta z).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1))) := by
  let s : ((Δ[1] : SSet.{u}) ⊗ zeroSourceCofibers z) _⦋1⦌ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (zeroSourceTheta_projection z)
    (Opposite.op ⦋1⦌)) s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (cofiberProjection C)).reflects_isInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((zeroSourceTheta z).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1)))
  have hi := (zeroSourceThetaInput_isInvertible z b).map (fixedSourceArrowsι z.vertex)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 hi

/-- 概要：大域的な θ を第二因子を時刻とする単体ホモトピーにする。
方針：二因子を交換して証明済みの両端を使う。
規約：元の θ の全高次単体を保持。使われ方：Ar の可変時刻での評価。 -/
def zeroSourceThetaHomotopy {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) :
    SSet.Homotopy (zeroSourceCofibersι z) (zeroSourceCofibersCanonical z) where
  h := (β_ (zeroSourceCofibers z) (Δ[1] : SSet.{u})).hom ≫ zeroSourceTheta z
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (zeroSourceCofibers z) ≫ zeroSourceTheta z = _
    exact zeroSourceTheta_zero z
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (zeroSourceCofibers z) ≫ zeroSourceTheta z = _
    exact zeroSourceTheta_one z
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

/-- 概要：ホモトピーとして表した θ の各頂点での辺も可逆。
方針：二因子の交換後の辺は元の θ の同じ辺。
規約：全ての頂点を含む。使われ方：関手同型による gapped 性の輸送。 -/
lemma zeroSourceThetaHomotopy_isInvertible {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (b : (zeroSourceCofibers z) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroSourceThetaHomotopy z) b).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ?_).2 (zeroSourceTheta_isInvertible z b)
  change (zeroSourceThetaHomotopy z).h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (zeroSourceCofibers z)) b).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one b]
  rfl

/-- 概要：θ を Ar の可変時刻で評価した図式は gapped。
方針：元の cofiber 図式との関手同型に沿って gapped 条件を移す。
規約：入力空間の安定性は不要。使われ方：第二の θ の object S 値の単体。 -/
lemma zeroSourceTheta_variableTime_isGapped {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C)
    (F : arNerve n ⟶ zeroSourceCofibers z) (hF : IsGapped (F ≫ zeroSourceCofibersι z))
    (τ : arNerve n ⟶ (Δ[1] : SSet.{u})) :
    IsGapped (variableTimeImage (zeroSourceThetaHomotopy z) F τ) :=
  hF.of_functorIso (variableTimeImageIso (zeroSourceThetaHomotopy z)
    (zeroSourceThetaHomotopy_isInvertible z) F τ)

/-- 概要：θ の可変時刻の評価でも subobject は指定零対象で厳密に一定。
方針：グラフでの前合成と大域的な θ の subobject の固定。
規約：時刻は Ar の任意の射。使われ方：左 fiber の条件。 -/
lemma zeroSourceTheta_variableTime_source {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (F : A ⟶ zeroSourceCofibers z) (τ : A ⟶ (Δ[1] : SSet.{u})) :
    variableTimeImage (zeroSourceThetaHomotopy z) F τ ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const z.vertex := by
  change (lift F τ ≫ (β_ (zeroSourceCofibers z) (Δ[1] : SSet.{u})).hom ≫ zeroSourceTheta z) ≫
    cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  simp only [Category.assoc]
  rw [zeroSourceTheta_source, SSet.comp_const, SSet.comp_const]

end SerrePositivity.KST.SConstruction
