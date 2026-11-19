module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointModelComparison

/-!
概要：二方向の実端点図式を、両パラメータ全体に沿う二つの loop 図式族にする。
方針：元の四次元図式を座標の組替えだけで curry し、元の各面を厳密回収する。
規約：面ごとに比較を独立選択しない。保持済み補正との一致は別途証明する。
使われ方：第二パラメータの全単体整合を保つ模型比較の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

section
variable {A P Q X : SSet.{u}} (H : A ⟶ (ihom (P ⊗ Q)).obj X)

/-- 入力と第二パラメータを一緒に動かし、第一パラメータの全図式を回収する。 -/
def d3BiDiagramJointLeft : A ⊗ Q ⟶ (ihom P).obj X :=
  curry (lift (lift (fst P (A ⊗ Q)) (snd P (A ⊗ Q) ≫ snd A Q))
    (snd P (A ⊗ Q) ≫ fst A Q) ≫ uncurry H)

/-- 第二パラメータを固定すると、元の同じ全図式の指定面そのものになる。 -/
lemma d3BiDiagramJointLeft_face (q : Q _⦋0⦌) :
    lift (𝟙 A) (SSet.const q) ≫ d3BiDiagramJointLeft H =
      H ≫ (pre (lift (𝟙 P) (SSet.const q))).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left, d3BiDiagramJointLeft, uncurry_curry, uncurry_pre_app]
  simp only [← Category.assoc]
  congr 1
end

/-- 元の第二四角形全体に沿う、第一方向の実四角形族。 -/
def d3DoubleEndpointJointLeftSquare :
    PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  d3BiDiagramJointLeft d3DoubleEndpointSquare

/-- 第二四角形の任意の角で、元の第一方向の全実面を厳密に保持する。 -/
lemma d3DoubleEndpointJointLeftSquare_face (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      d3DoubleEndpointJointLeftSquare =
    d3DoubleEndpointSquare ≫ (pre (d3BiParameterLeftFace k l)).app PointedKanInfinity :=
  d3BiDiagramJointLeft_face _ _

/-- 同じ共同族の各頂点は、元の実面の認証済み loop 図式。 -/
lemma d3DoubleEndpointJointLeftSquare_isLoop
    (v : (PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3DoubleEndpointJointLeftSquare.app _ v) := by
  obtain ⟨y, a, b⟩ := v
  let k : Fin 2 := stdSimplex.obj₀Equiv a
  let l : Fin 2 := stdSimplex.obj₀Equiv b
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (d3DoubleEndpointJointLeftSquare_face k l) (Opposite.op ⦋0⦌)) y
  have ha : stdSimplex.obj₀Equiv.symm k = a := Equiv.symm_apply_apply _ _
  have hb : stdSimplex.obj₀Equiv.symm l = b := Equiv.symm_apply_apply _ _
  change d3DoubleEndpointJointLeftSquare.app _
    (y, (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) = _ at h
  rw [ha, hb] at h
  rw [h]
  exact d3DoubleEndpointLeftFace_isLoop k l y

/-- 一つの全パラメータ作用として保持した、第一方向の実 loop 全図式族。 -/
def d3DoubleEndpointJointLeftLoopFamily :
    PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex d3DoubleEndpointJointLeftSquare
    d3DoubleEndpointJointLeftSquare_isLoop

lemma d3DoubleEndpointJointLeftLoopFamily_ι :
    d3DoubleEndpointJointLeftLoopFamily.{u} ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    d3DoubleEndpointJointLeftSquare := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 共同 loop 族の角制限は、以前の同じ実面 loop 族に全単体で一致する。 -/
lemma d3DoubleEndpointJointLeftLoopFamily_face (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      d3DoubleEndpointJointLeftLoopFamily = d3DoubleEndpointLeftLoopFamily k l := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).1
  rw [Category.assoc, d3DoubleEndpointJointLeftLoopFamily_ι,
    d3DoubleEndpointLeftLoopFamily_ι, d3DoubleEndpointJointLeftSquare_face]

/-- 第二パラメータの全単体を同時に保つ、厳密な実終点上の標準模型比較。 -/
def d3DoubleEndpointJointLeftModelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3DoubleEndpointJointLeftLoopFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ d3PointedKanLoopSection)
      d3DoubleEndpointJointLeftLoopFamily :=
  d3KanLoopDiagramIsoOverTarget _ _ (Iso.refl _)

/-- 一つの共同模型比較の終点成分は、共同実終点上の恒等同型そのもの。 -/
lemma d3DoubleEndpointJointLeftModelIso_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointLeftModelIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target (d3DoubleEndpointJointLeftLoopFamily ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) rfl = Iso.refl _ :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

section
variable {A P Q X : SSet.{u}} (H : A ⟶ (ihom (P ⊗ Q)).obj X)

/-- 入力と第一パラメータを同時に動かす、第二方向の全図式。 -/
def d3BiDiagramJointRight : A ⊗ P ⟶ (ihom Q).obj X :=
  curry (lift (lift (snd Q (A ⊗ P) ≫ snd A P) (fst Q (A ⊗ P)))
    (snd Q (A ⊗ P) ≫ fst A P) ≫ uncurry H)

/-- 第一パラメータの固定は、元の同じ第二方向の全実面を回収する。 -/
lemma d3BiDiagramJointRight_face (p : P _⦋0⦌) :
    lift (𝟙 A) (SSet.const p) ≫ d3BiDiagramJointRight H =
      H ≫ (pre (lift (SSet.const p) (𝟙 Q))).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left, d3BiDiagramJointRight, uncurry_curry, uncurry_pre_app]
  simp only [← Category.assoc]
  congr 1
end

/-- 元の第一四角形全体に沿う、第二方向の実四角形族。 -/
def d3DoubleEndpointJointRightSquare :
    PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  d3BiDiagramJointRight d3DoubleEndpointSquare

/-- 第一四角形の任意の角で、元の第二方向の全実面を厳密に保持する。 -/
lemma d3DoubleEndpointJointRightSquare_face (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      d3DoubleEndpointJointRightSquare =
    d3DoubleEndpointSquare ≫ (pre (d3BiParameterRightFace k l)).app PointedKanInfinity :=
  d3BiDiagramJointRight_face _ _

/-- 同じ共同族の各頂点は、元の実面の認証済み loop 図式。 -/
lemma d3DoubleEndpointJointRightSquare_isLoop
    (v : (PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3DoubleEndpointJointRightSquare.app _ v) := by
  obtain ⟨y, a, b⟩ := v
  let k : Fin 2 := stdSimplex.obj₀Equiv a
  let l : Fin 2 := stdSimplex.obj₀Equiv b
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (d3DoubleEndpointJointRightSquare_face k l) (Opposite.op ⦋0⦌)) y
  have ha : stdSimplex.obj₀Equiv.symm k = a := Equiv.symm_apply_apply _ _
  have hb : stdSimplex.obj₀Equiv.symm l = b := Equiv.symm_apply_apply _ _
  change d3DoubleEndpointJointRightSquare.app _
    (y, (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) = _ at h
  rw [ha, hb] at h
  rw [h]
  exact d3DoubleEndpointRightFace_isLoop k l y

/-- 一つの全パラメータ作用として保持した、第二方向の実 loop 全図式族。 -/
def d3DoubleEndpointJointRightLoopFamily :
    PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex d3DoubleEndpointJointRightSquare
    d3DoubleEndpointJointRightSquare_isLoop

lemma d3DoubleEndpointJointRightLoopFamily_ι :
    d3DoubleEndpointJointRightLoopFamily.{u} ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    d3DoubleEndpointJointRightSquare := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 共同 loop 族の角制限は、以前の同じ実面 loop 族に全単体で一致する。 -/
lemma d3DoubleEndpointJointRightLoopFamily_face (k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) ≫
      d3DoubleEndpointJointRightLoopFamily = d3DoubleEndpointRightLoopFamily k l := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).1
  rw [Category.assoc, d3DoubleEndpointJointRightLoopFamily_ι,
    d3DoubleEndpointRightLoopFamily_ι, d3DoubleEndpointJointRightSquare_face]

/-- 第一パラメータの全単体を同時に保つ、厳密な実終点上の標準模型比較。 -/
def d3DoubleEndpointJointRightModelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3DoubleEndpointJointRightLoopFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ d3PointedKanLoopSection)
      d3DoubleEndpointJointRightLoopFamily :=
  d3KanLoopDiagramIsoOverTarget _ _ (Iso.refl _)

/-- 一つの共同模型比較の終点成分は、共同実終点上の恒等同型そのもの。 -/
lemma d3DoubleEndpointJointRightModelIso_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointRightModelIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target (d3DoubleEndpointJointRightLoopFamily ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) rfl = Iso.refl _ :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

section
variable {A P Q X : SSet.{u}} (H : A ⟶ (ihom (P ⊗ Q)).obj X)

/-- 第一方向の角評価は、元の他方向の面の全共同評価と一致する。 -/
lemma d3BiDiagramJointLeft_corner (p : P _⦋0⦌) :
    d3BiDiagramJointLeft H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p =
      (β_ A Q).hom ≫ uncurry (H ≫ (pre (lift (SSet.const p) (𝟙 Q))).app X) := by
  rw [d3BiDiagramJointLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, uncurry_pre_app]
  simp only [← Category.assoc]
  congr 1

/-- 第二方向の角評価も、元の第一方向の面の全共同評価そのもの。 -/
lemma d3BiDiagramJointRight_corner (q : Q _⦋0⦌) :
    d3BiDiagramJointRight H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt q =
      (β_ A P).hom ≫ uncurry (H ≫ (pre (lift (𝟙 P) (SSet.const q))).app X) := by
  rw [d3BiDiagramJointRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, uncurry_pre_app]
  simp only [← Category.assoc]
  congr 1
end

/-- 第一方向共同族の各角は、同じ実第二方向族の全共同評価である。 -/
lemma d3DoubleEndpointJointLeftLoopFamily_corner (i j : Fin 2) :
    d3DoubleEndpointJointLeftLoopFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j =
    (β_ PointedKanInfinity ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).hom ≫
      uncurry (d3DoubleEndpointRightLoopFamily i j ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointJointLeftLoopFamily_ι,
    d3DoubleEndpointRightLoopFamily_ι]
  exact d3BiDiagramJointLeft_corner _ _

/-- 第二方向共同族の各角も、同じ実第一方向族の全共同評価を回収する。 -/
lemma d3DoubleEndpointJointRightLoopFamily_corner (i j : Fin 2) :
    d3DoubleEndpointJointRightLoopFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j =
    (β_ PointedKanInfinity ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).hom ≫
      uncurry (d3DoubleEndpointLeftLoopFamily i j ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointJointRightLoopFamily_ι,
    d3DoubleEndpointLeftLoopFamily_ι]
  exact d3BiDiagramJointRight_corner _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
