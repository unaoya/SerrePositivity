module
public import SerrePositivity.KST.SConstruction.McCarthyThetaFiber

/-! # θ の両端と切断への実ホモトピー
概要：左 fiber 内の θ の始点は ρ の終端、終点は quotient と切断の合成。
方針：可変時刻の両端と元の quotient の厳密な回収を二射影で照合する。
規約：頂点だけの比較ではない。使われ方：McCarthy の左 fiber の弱同値。
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

/-- 概要：θ の入力図式の quotient は元の左 fiber の quotient の実図式。
方針：ρ の終端で quotient が厳密に固定されることを使う。
規約：元の quotient を変更しない。使われ方：θ の切断側の端点。 -/
lemma mcCarthyThetaDiagram_quotient (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    mcCarthyThetaDiagram X a e ≫ zeroSourceCofibersQuotient (objectSLastDiagonalZeroVertex a) =
      gappedDiagram ((cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e) := by
  have hq := ConcreteCategory.congr_hom (NatTrans.congr_app
    (mcCarthyRhoTerminal_quotient X a) (Opposite.op ⦋n⦌)) e
  change (objectSConstructionFunctor.map (cofiberStableQuotient X)).app (Opposite.op ⦋n⦌)
    ((simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app
      (Opposite.op ⦋n⦌) ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e)) =
    (cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e at hq
  have hd := congrArg gappedDiagram hq
  rw [gappedDiagram_objectSFunctor_map] at hd
  change mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) = _ at hd
  simp only [zeroSourceCofibersQuotient, ← Category.assoc]
  rw [mcCarthyThetaDiagram_ι]
  simpa only [Category.assoc] using hd

/-- 概要：θ の object S 値の零時刻は ρ の終端の図式。
方針：可変時刻零の式と入力図式の包含の式。
規約：図式全体を厳密に回収。使われ方：左 fiber の始点。 -/
lemma mcCarthyThetaObjectMap_zero (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ mcCarthyThetaObjectMap X a =
        mcCarthyRhoTerminal X a ≫ simplexLeftFiberProjection
          (objectSConstructionFunctor.map (cofiberStableSubobject X)) a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro e
  apply gappedDiagram_injective
  change gappedDiagram (mcCarthyThetaObjectVertex X a e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n)) =
      mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e)
  rw [mcCarthyThetaObjectVertex_diagram, arTimeCoordinate_constant, variableTimeImage_zero,
    mcCarthyThetaDiagram_ι]

/-- 概要：θ の object S 値の一時刻は元の quotient の標準 ι 型。
方針：可変時刻一の式と quotient の厳密な回収。
規約：元の標準零 cofiber 関手の像。使われ方：左 fiber の切断側の終点。 -/
lemma mcCarthyThetaObjectMap_one (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ mcCarthyThetaObjectMap X a =
        cofiberLeftFiberQuotient X a ≫ objectSConstructionFunctor.map
          (zeroCofiberStableFunctor X (objectSLastDiagonalZeroVertex a) true) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro e
  apply gappedDiagram_injective
  change gappedDiagram (mcCarthyThetaObjectVertex X a e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n)) =
      gappedDiagram ((objectSConstructionFunctor.map
        (zeroCofiberStableFunctor X (objectSLastDiagonalZeroVertex a) true)).app (Opposite.op ⦋n⦌)
          ((cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e))
  rw [mcCarthyThetaObjectVertex_diagram, arTimeCoordinate_constant, variableTimeImage_one,
    gappedDiagram_objectSFunctor_map]
  change mcCarthyThetaDiagram X a e ≫ zeroSourceCofibersQuotient
    (objectSLastDiagonalZeroVertex a) ≫
      zeroCofiberFunctor (objectSLastDiagonalZeroVertex a) true = _
  rw [← Category.assoc, mcCarthyThetaDiagram_quotient]
  rfl

/-- 概要：左 fiber 値の θ の零時刻は ρ の終端。
方針：元の図式と最後の頂点のパラメーターを二射影で照合する。
規約：strict pullback 内の厳密な等号。使われ方：第二ホモトピーの始点。 -/
lemma mcCarthyThetaFiberMap_zero (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ mcCarthyThetaFiberMap X a =
        mcCarthyRhoTerminal X a := by
  apply simplexLeftFiber_hom_ext (objectSConstructionFunctor.map (cofiberStableSubobject X)) a
  · rw [Category.assoc, mcCarthyThetaFiberMap_projection, mcCarthyThetaObjectMap_zero]
  · rw [Category.assoc, mcCarthyThetaFiberMap_parameter, SSet.comp_const,
      mcCarthyRhoTerminal_parameter]

/-- 概要：左 fiber 値の θ の一時刻は quotient と切断の合成。
方針：標準 ι 型の図式と定値パラメーターを二射影で厳密に回収する。
規約：同型に弱めない。使われ方：左 fiber のホモトピー逆の比較。 -/
lemma mcCarthyThetaFiberMap_one (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ mcCarthyThetaFiberMap X a =
        cofiberLeftFiberQuotient X a ≫ mcCarthyFiberSection X a := by
  apply simplexLeftFiber_hom_ext (objectSConstructionFunctor.map (cofiberStableSubobject X)) a
  · rw [Category.assoc, mcCarthyThetaFiberMap_projection, mcCarthyThetaObjectMap_one,
      Category.assoc, mcCarthyFiberSection_projection]
  · rw [Category.assoc, mcCarthyThetaFiberMap_parameter, SSet.comp_const,
      Category.assoc, mcCarthyFiberSection_parameter, SSet.comp_const]

/-- 概要：θ は ρ の終端から quotient と切断の合成への実際の単体ホモトピー。
方針：構成した左 fiber 内の族と証明した両端を組にする。
規約：未証明の収縮性は仮定しない。使われ方：McCarthy の quotient 射の弱同値。 -/
def mcCarthyThetaFiberHomotopy (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    SSet.Homotopy (mcCarthyRhoTerminal X a)
      (cofiberLeftFiberQuotient X a ≫ mcCarthyFiberSection X a) where
  h := mcCarthyThetaFiberMap X a
  h₀ := mcCarthyThetaFiberMap_zero X a
  h₁ := mcCarthyThetaFiberMap_one X a
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end SerrePositivity.KST.SConstruction
