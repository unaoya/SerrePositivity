module
public import SerrePositivity.KST.SConstruction.McCarthyRhoFiber

/-! # 恒等射から McCarthy の零 subobject 側への実ホモトピー
概要：左 fiber の ρ は恒等射から零 subobject 側への単体ホモトピーとなり、quotient を固定する。
方針：元の C 内の正規化の厳密な両端を pullback の二射影で照合する。
規約：第二の θ による切断との比較は別工程。使われ方：McCarthy の変形収縮。
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

/-- 概要：ρ の object S 値の零時刻は元の cofiber 図式への射影。
方針：全単体で元の ρ の零時刻の厳密回収を使う。
規約：元の図式そのものを回収する。使われ方：実ホモトピーの恒等端点。 -/
lemma mcCarthyRhoFiberObjectMap_zero (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ mcCarthyRhoFiberObjectMap X a =
        simplexLeftFiberProjection
          (objectSConstructionFunctor.map (cofiberStableSubobject X)) a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro e
  apply gappedDiagram_injective
  change gappedDiagram (mcCarthyRhoFiberObjectVertex X a e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n)) = mcCarthyFiberDiagram X a e
  rw [mcCarthyRhoFiberObjectVertex_diagram]
  exact mcCarthyRho_timeZero _ _ _ _ _

/-- 概要：ρ のパラメーターの端点は元のパラメーターに収縮の端点を合成したもの。
方針：二因子交換と定値時刻を各単体で計算する。
規約：両時刻に共通の厳密な等号。使われ方：左 fiber の両端のパラメーター。 -/
lemma mcCarthyRhoFiberParameterMap_endpoint (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (i : Fin 2) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a)) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
      mcCarthyRhoFiberParameterMap X a =
        simplexLeftFiberParameter (objectSConstructionFunctor.map (cofiberStableSubobject X)) a ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Δ[m] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction m := by
  unfold mcCarthyRhoFiberParameterMap
  simp only [← Category.assoc]
  congr 1

/-- 概要：ρ の左 fiber 値の零時刻は恒等射。
方針：図式とパラメーターの両射影を厳密に回収する。
規約：単体ホモトピーの実際の端点の等号。使われ方：ρ のホモトピー構造。 -/
lemma mcCarthyRhoFiberMap_zero (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    lift (𝟙 (cofiberSubobjectLeftFiber X a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ mcCarthyRhoFiberMap X a = 𝟙 _ := by
  apply simplexLeftFiber_hom_ext (objectSConstructionFunctor.map (cofiberStableSubobject X)) a
  · rw [Category.assoc, mcCarthyRhoFiberMap_projection, mcCarthyRhoFiberObjectMap_zero,
      Category.id_comp]
  · rw [Category.assoc, mcCarthyRhoFiberMap_parameter, mcCarthyRhoFiberParameterMap_endpoint,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero, Category.comp_id, Category.id_comp]

/-- 概要：ρ の一時刻で得られる同じ左 fiber の自己射。
方針：構成した族を時刻一で制限する。
規約：切断との同一視は第二の θ を待つ。使われ方：第一ホモトピーの終点。 -/
def mcCarthyRhoTerminal (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⟶ cofiberSubobjectLeftFiber X a :=
  lift (𝟙 (cofiberSubobjectLeftFiber X a))
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ mcCarthyRhoFiberMap X a

/-- 概要：ρ は恒等射から構成した終端射への実際の単体ホモトピー。
方針：strict pullback 内の族と証明した零端点を使う。
規約：ホモトピーの存在を追加仮定にしない。使われ方：左 fiber の変形収縮。 -/
def mcCarthyRhoFiberHomotopy (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    SSet.Homotopy (𝟙 (cofiberSubobjectLeftFiber X a)) (mcCarthyRhoTerminal X a) where
  h := mcCarthyRhoFiberMap X a
  h₀ := mcCarthyRhoFiberMap_zero X a
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：ρ の全時刻で quotient への射は元の値に固定される。
方針：object S の単体を図式に戻し、元の ρ の quotient の厳密回収を使う。
規約：射の厳密等号。使われ方：第二の θ と quotient 上での比較。 -/
lemma mcCarthyRhoFiberMap_quotient (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoFiberMap X a ≫ cofiberLeftFiberQuotient X a =
      fst (cofiberSubobjectLeftFiber X a) (Δ[1] : SSet.{u}) ≫ cofiberLeftFiberQuotient X a := by
  rw [cofiberLeftFiberQuotient, ← Category.assoc, mcCarthyRhoFiberMap_projection]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨e, τ⟩
  apply gappedDiagram_injective
  change gappedDiagram ((objectSConstructionFunctor.map (cofiberStableQuotient X)).app
    (Opposite.op ⦋n⦌) (mcCarthyRhoFiberObjectVertex X a e τ)) =
    gappedDiagram ((objectSConstructionFunctor.map (cofiberStableQuotient X)).app
      (Opposite.op ⦋n⦌) ((simplexLeftFiberProjection
        (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app (Opposite.op ⦋n⦌) e))
  rw [gappedDiagram_objectSFunctor_map, gappedDiagram_objectSFunctor_map,
    mcCarthyRhoFiberObjectVertex_diagram]
  exact mcCarthyRho_quotient _ _ _ _ _ _

/-- 概要：ρ の終端のパラメーターは最後の頂点に厳密に一定。
方針：収縮の時刻一の端点と pullback の射影の式。
規約：元の固定単体の最後の頂点。使われ方：第二の θ の零 subobject 条件。 -/
lemma mcCarthyRhoTerminal_parameter (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoTerminal X a ≫ simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
        SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m)) := by
  rw [mcCarthyRhoTerminal, Category.assoc, mcCarthyRhoFiberMap_parameter,
    mcCarthyRhoFiberParameterMap_endpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one, SSet.comp_const]

/-- 概要：ρ の終端の quotient 射は元の quotient 射。
方針：全時刻での quotient の固定を時刻一に制限する。
規約：射の厳密な等号。使われ方：第二の θ と切断との比較。 -/
lemma mcCarthyRhoTerminal_quotient (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoTerminal X a ≫ cofiberLeftFiberQuotient X a = cofiberLeftFiberQuotient X a := by
  rw [mcCarthyRhoTerminal, Category.assoc, mcCarthyRhoFiberMap_quotient]
  rw [← Category.assoc, lift_fst, Category.id_comp]

/-- 概要：ρ の終端の実図式の subobject は固定単体の最後の対角零対象で一定。
方針：終端のパラメーターの式を左 fiber の入力条件へ代入する。
規約：零対象への同型ではなく元の指定零対象への等号。使われ方：第二の θ の入力。 -/
lemma mcCarthyRhoTerminal_source (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    mcCarthyFiberDiagram X a ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) ≫
      cofiberProjection X.carrier ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          SSet.const (objectSLastDiagonalZeroVertex a).vertex := by
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (mcCarthyRhoTerminal_parameter X a) (Opposite.op ⦋n⦌)) e
  change mcCarthyFiberParameter X a
    ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last m)) n at hp
  have hs := mcCarthyFiberDiagram_source X a
    ((mcCarthyRhoTerminal X a).app (Opposite.op ⦋n⦌) e)
  rw [hp] at hs
  have hi : (stdSimplex.objEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last m)) n)).toOrderHom =
      OrderHom.const (Fin (n + 1)) (Fin.last m) := by
    ext j
    rfl
  rw [hi, arNerveMap_const, SSet.const_comp] at hs
  exact hs

end SerrePositivity.KST.SConstruction
