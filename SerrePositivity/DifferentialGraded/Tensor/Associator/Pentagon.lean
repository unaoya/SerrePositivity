module

public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-!
# Tensor.Associator.Pentagon

## 概要
五角 coherence と結合比較の射・パラメータ自然性、射影的 K-flat 比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t x

/-! ## ProjectiveComparison（旧 SerrePositivity/DifferentialGraded/Tensor/ProjectiveComparison.lean） -/

/-! # 射影的/semifree対象間の準同型のtensorによる保存 -/

@[expose] public section ProjectiveComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射影的対象間の準同型は、任意の左加群とのtensorでホモトピー同値になる。 -/
def rightTensorProjectiveHomotopyEquiv (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    HomotopyEquiv ((rightTensorFunctor A D L).obj M) ((rightTensorFunctor A D L).obj N) := by
  let Q := moduleToHomotopy A D
  have : IsIso (Q.map f) := moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  let g : N ⟶ M := Q.preimage (inv (Q.map f))
  have hg : Q.map g = inv (Q.map f) := Q.map_preimage _
  have hfg : Nonempty (ModuleHomotopy A D (f ≫ g) (𝟙 M)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (f ≫ g) = Q.map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hgf : Nonempty (ModuleHomotopy A D (g ≫ f) (𝟙 N)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (g ≫ f) = Q.map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  refine
    { hom := (rightTensorFunctor A D L).map f
      inv := (rightTensorFunctor A D L).map g
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · have ht := (rightTensorMap_homotopy A D L hfg.some).some
    change Homotopy ((rightTensorFunctor A D L).map (f ≫ g))
      ((rightTensorFunctor A D L).map (𝟙 M)) at ht
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using ht
  · have ht := (rightTensorMap_homotopy A D L hgf.some).some
    change Homotopy ((rightTensorFunctor A D L).map (g ≫ f))
      ((rightTensorFunctor A D L).map (𝟙 N)) at ht
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using ht

lemma rightTensor_projective_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso ((rightTensorFunctor A D L).map f) :=
  (rightTensorProjectiveHomotopyEquiv A D L hM hN f hf).quasiIso_hom

/-- semifree解像度同士の準同型は、左加群にflat条件を課さずtensorで準同型になる。 -/
lemma rightTensor_semifree_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleSemifree A D M) (hN : moduleSemifree A D N) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : QuasiIso ((rightTensorFunctor A D L).map f) :=
  rightTensor_projective_quasiIso A D L
    (moduleSemifree_homotopicallyProjective A D hM)
    (moduleSemifree_homotopicallyProjective A D hN) f hf

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ProjectiveComparison

/-! ## ProjectiveKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/ProjectiveKFlat.lean） -/

/-! # 主Homによる射影性から相対K-flat性への橋渡し -/

@[expose] public section ProjectiveKFlat

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全Hom endによるhomotopical projectivityは相対K-flat性を含意する。 -/
lemma moduleHomotopicallyProjective_relativeKFlat {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨P, q, hP, hk, _, hq⟩ := exists_relativeKFlat_resolution A D M
  intro L hL
  exact cochainAcyclic_of_homotopyEquiv (hk L hL)
    (BalancedTensor.rightTensorProjectiveHomotopyEquiv A D L
      (moduleSemifree_homotopicallyProjective A D hP) hM q hq)

end SerrePositivity.DifferentialGraded
end

end ProjectiveKFlat

/-! ## PentagonLongElements（旧 SerrePositivity/DifferentialGraded/Tensor/PentagonLongElements.lean） -/

/-! # 五角の三辺からなる経路の四重生成元上の評価 -/

@[expose] public section PentagonLongElements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
variable (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (S : Bimodule A F G)

lemma pentagonLongFirst_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s i m z n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) (hz : k + r = z) :
    composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g n
      (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn) =
    associatorLeftElement A B C F G P (compose A C E F Q R) S b c f g σ
      (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e τ q hz) v (by omega) hn := by
  exact composeMapComponent_element_of_values A B F G
    (associatorIso A B C E F P Q R).hom (𝟙 (BimoduleCategory.of A F G S)) b f g
    σ (associatorLeftElement A B C E F P Q R b c e f τ q v hi hm)
    σ (associatorRightElement A B C E F P Q R b c e f
      (l := z) (n := m) τ q v hz (by omega)) hn
    (BimoduleCategory.valueMap_id_apply A F G (BimoduleCategory.of A F G S) f g a σ)
    (associatorIso_hom_value_element A B C E F P Q R b c e f τ q v hi hz hm)

lemma pentagonLongThird_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s z j l n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hz : k + r = z) (hj : a + z = j) (hl : a + k = l) (hn : j + s = n) :
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (quadMiddleElement A B C E F G P Q R S b c e f g σ τ q v hz hj hn) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl (by omega) hn := by
  exact composeMapComponent_element_of_values A B C G
    (𝟙 (BimoduleCategory.of A B C P)) (associatorIso A C E F G Q R S).hom b c g
    (associatorLeftElement A C E F G Q R S c e f g σ τ q hz hj) v
    (associatorRightElement A C E F G Q R S c e f g
      (l := l) (n := j) σ τ q hl (by omega)) v hn
    (associatorIso_hom_value_element A C E F G Q R S c e f g σ τ q hz hl hj)
    (BimoduleCategory.valueMap_id_apply A B C (BimoduleCategory.of A B C P) b c s v)

lemma pentagonLong_component_element (b : B) (c : C) (e : E) (f : F) (g : G)
    {a k r s i m l j n : ℤ} (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n)
    (hl : a + k = l) (hj : l + r = j) :
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n
        (composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
          (𝟙 (BimoduleCategory.of A F G S)) b g n
          (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn))) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl hj (by omega) := by
  have h₁ := pentagonLongFirst_element A B C E F G P Q R S b c e f g
    (z := k + r) σ τ q v hi hm hn rfl
  have h₂ := associatorValueComponent_element A B C F G P (compose A C E F Q R) S b c f g
    (k := a) (r := k + r) (s := s) (i := m) (l := j) (n := n) σ
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e τ q rfl) v
    (by omega) (by omega) hn
  have h₁₂ := (congrArg
    (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n) h₁).trans h₂
  have h₃ := pentagonLongThird_element A B C E F G P Q R S b c e f g
    (z := k + r) (j := j) (l := l) (n := n) σ τ q v rfl (by omega) hl (by omega)
  exact (congrArg (composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
    (associatorIso A C E F G Q R S).hom b g n) h₁₂).trans h₃

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end PentagonLongElements

/-! ## PentagonShortElements（旧 SerrePositivity/DifferentialGraded/Tensor/PentagonShortElements.lean） -/

/-! # 五角の二辺からなる経路の四重生成元上の評価 -/

@[expose] public section PentagonShortElements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma pentagonShort_component_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s i m l j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n)
    (hl : a + k = l) (hj : l + r = j) :
    associatorValueComponent A B C E G P Q (compose A E F G R S) b g n
      (associatorValueComponent A B E F G (compose A B C E P Q) R S b g n
        (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl hj (by omega) := by
  have h₁ := associatorValueComponent_element A B E F G (compose A B C E P Q) R S b e f g
    (k := a) (r := k) (s := i) (i := m) (l := l) (n := n) σ τ
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm hl hn
  have h₂ := associatorValueComponent_element A B C E G P Q (compose A E F G R S) b c e g
    (k := l) (r := r) (s := s) (i := i) (l := j) (n := n)
    (BalancedTensor.element A F (S.rightAt g) (R.leftAt e) f σ τ hl) q v hi hj (by omega)
  exact (congrArg (associatorValueComponent A B C E G P Q (compose A E F G R S) b g n) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end PentagonShortElements

/-! ## Pentagon（旧 SerrePositivity/DifferentialGraded/Tensor/Pentagon.lean） -/

/-! # 全Hom自然なbimodule合成の五角coherence -/

@[expose] public section Pentagon

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
variable (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (S : Bimodule A F G)

/-- 固定成分による値のchain mapとしての五角。 -/
lemma pentagonValueHom (b : B) (g : G) :
    associatorValueHom A B E F G (compose A B C E P Q) R S b g ≫
      associatorValueHom A B C E G P Q (compose A E F G R S) b g =
    composeValueHom A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g ≫
      associatorValueHom A B C F G P (compose A C E F Q R) S b g ≫
      composeValueHom A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom b g := by
  apply Cochain.ofHom_injective
  apply quadLeft_cochain_element_ext A B C E F G P Q R S b g
  intro c e f a k r s i m n t hi hm hn ht σ τ q v
  simp only [add_zero] at ht
  cases ht
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E G P Q (compose A E F G R S) b g n
    (associatorValueComponent A B E F G (compose A B C E P Q) R S b g n
      (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)) =
    composeMapComponent A B C G (𝟙 (BimoduleCategory.of A B C P))
      (associatorIso A C E F G Q R S).hom b g n
      (associatorValueComponent A B C F G P (compose A C E F Q R) S b g n
        (composeMapComponent A B F G (associatorIso A B C E F P Q R).hom
          (𝟙 (BimoduleCategory.of A F G S)) b g n
          (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)))
  exact (pentagonShort_component_element A B C E F G P Q R S b c e f g
    (l := a + k) (j := a + k + r) σ τ q v hi hm hn rfl rfl).trans
    (pentagonLong_component_element A B C E F G P Q R S b c e f g
      (l := a + k) (j := a + k + r) σ τ q v hi hm hn rfl rfl).symm

/-- 元の値の結合同型と合成mapに対する五角。 -/
lemma pentagonValue (b : B) (g : G) :
    (associatorValueIso A B E F G (compose A B C E P Q) R S b g).hom ≫
      (associatorValueIso A B C E G P Q (compose A E F G R S) b g).hom =
    composeValueMap A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) b g ≫
      (associatorValueIso A B C F G P (compose A C E F Q R) S b g).hom ≫
      composeValueMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom b g := by
  simpa only [associatorValueHom_eq, composeValueHom_eq] using
    pentagonValueHom A B C E F G P Q R S b g

/-- 実際の閉零bimodule射としての結合同型の五角。 -/
lemma pentagon :
    (associatorIso A B E F G (compose A B C E P Q) R S).hom ≫
      (associatorIso A B C E G P Q (compose A E F G R S)).hom =
    composeMap A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) ≫
      (associatorIso A B C F G P (compose A C E F Q R) S).hom ≫
      composeMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom := by
  apply BimoduleCategory.value_hom_ext A B G
  intro b g
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact pentagonValue A B C E F G P Q R S b g

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end Pentagon

/-! ## AssociatorMapElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMapElements.lean） -/

/-! # 閉零bimodule射の三変数に関する結合比較の生成元自然性 -/

@[expose] public section AssociatorMapElements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "Q₁" => BimoduleCategory.underlying A C E Q'
local notation "R₀" => BimoduleCategory.underlying A E F R
local notation "R₁" => BimoduleCategory.underlying A E F R'

lemma associatorComponent_map_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i l n : ℤ}
    (τ : ((R₀).value e d).X k) (q : ((Q₀).value c e).X r) (v : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E F P₁ Q₁ R₁ b d n
      (composeMapComponent A B E F (composeMap A B C E f g) h b d n
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hn)) =
    composeMapComponent A B C F f (composeMap A C E F g h) b d n
      (associatorValueComponent A B C E F P₀ Q₀ R₀ b d n
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hn)) := by
  have hS := leftTripleComponent_element A B C E F f g h b c e d τ q v hi hn
  have hA := associatorValueComponent_element A B C E F P₀ Q₀ R₀ b c e d
    (k := k) (r := r) (s := s) (i := i) (l := l) (n := n) τ q v hi hl hn
  have hB := associatorValueComponent_element A B C E F P₁ Q₁ R₁ b c e d
    (k := k) (r := r) (s := s) (i := i) (l := l) (n := n)
    (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
    (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hl hn
  have hR := rightTripleComponent_element A B C E F f g h b c e d
    (k := k) (r := r) (s := s) (l := l) (n := n) τ q v hl (by omega)
  exact element_square
    (associatorValueComponent A B C E F P₀ Q₀ R₀ b d n)
    (associatorValueComponent A B C E F P₁ Q₁ R₁ b d n)
    (composeMapComponent A B E F (composeMap A B C E f g) h b d n)
    (composeMapComponent A B C F f (composeMap A C E F g h) b d n)
    _ _ _ _ hS hA hB hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMapElements

/-! ## AssociatorMapNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMapNaturality.lean） -/

/-! # 閉零bimodule射の三変数に関する結合比較の生成元自然性 -/

@[expose] public section AssociatorMapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "Q₁" => BimoduleCategory.underlying A C E Q'
local notation "R₀" => BimoduleCategory.underlying A E F R
local notation "R₁" => BimoduleCategory.underlying A E F R'

lemma associatorValueHom_map_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (d : F) :
    composeValueHom A B E F (composeMap A B C E f g) h b d ≫
      associatorValueHom A B C E F P₁ Q₁ R₁ b d =
    associatorValueHom A B C E F P₀ Q₀ R₀ b d ≫
      composeValueHom A B C F f (composeMap A C E F g h) b d := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B C E F P₀ Q₀ R₀ b d
  intro c e k r s i m n hi hm hn τ q v
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E F P₁ Q₁ R₁ b d m
    (composeMapComponent A B E F (composeMap A B C E f g) h b d m
      (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hm)) =
    composeMapComponent A B C F f (composeMap A C E F g h) b d m
      (associatorValueComponent A B C E F P₀ Q₀ R₀ b d m
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hm))
  exact associatorComponent_map_element A B C E F f g h b c e d
    (l := k + r) τ q v hi rfl hm

/-- 値のchain mapとしての、元の結合同型の閉零三変数自然性。 -/
lemma associatorValue_map_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (d : F) :
    composeValueMap A B E F (composeMap A B C E f g) h b d ≫
      (associatorValueIso A B C E F P₁ Q₁ R₁ b d).hom =
    (associatorValueIso A B C E F P₀ Q₀ R₀ b d).hom ≫
      composeValueMap A B C F f (composeMap A C E F g h) b d := by
  simpa only [composeValueHom_eq, associatorValueHom_eq] using
    associatorValueHom_map_naturality A B C E F f g h b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMapNaturality

/-! ## AssociatorNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorNaturality.lean） -/

/-! # 閉零bimodule射の三変数に関する結合比較の生成元自然性 -/

@[expose] public section AssociatorNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "Q₁" => BimoduleCategory.underlying A C E Q'
local notation "R₀" => BimoduleCategory.underlying A E F R
local notation "R₁" => BimoduleCategory.underlying A E F R'

/-- 実際の閉零bimodule射の三変数についての結合同型の自然性。 -/
lemma associatorIso_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    composeMap A B E F (composeMap A B C E f g) h ≫
      (associatorIso A B C E F P₁ Q₁ R₁).hom =
    (associatorIso A B C E F P₀ Q₀ R₀).hom ≫
      composeMap A B C F f (composeMap A C E F g h) := by
  apply BimoduleCategory.value_hom_ext A B F
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact associatorValue_map_naturality A B C E F f g h b d

/-- 二通りの反復合成の、閉零bimodule圏における三変数自然同型。 -/
def associatorNatIso : leftTripleFunctor A B C E F ≅ rightTripleFunctor A B C E F :=
  NatIso.ofComponents
    (fun X => associatorIso A B C E F (BimoduleCategory.underlying A B C X.1.1)
      (BimoduleCategory.underlying A C E X.1.2) (BimoduleCategory.underlying A E F X.2))
    (fun f => associatorIso_naturality A B C E F f.1.1 f.1.2 f.2)

@[simp]
lemma associatorNatIso_app
    (X : (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F) :
    (associatorNatIso A B C E F).app X =
      associatorIso A B C E F (BimoduleCategory.underlying A B C X.1.1)
        (BimoduleCategory.underlying A C E X.1.2) (BimoduleCategory.underlying A E F X.2) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorNaturality

/-! ## AssociatorParameterValues（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorParameterValues.lean） -/

/-! # 結合比較の各bimodule変数に関する任意パラメータ自然性 -/

@[expose] public section AssociatorParameterValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A}

lemma associator_firstParam_value {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P') (b : B) (f : F) :
    firstParamHom A B E F R (firstParam A B C E Q τ) b f ≫
      homPostcompose _ (associatorValueHom A B C E F P' Q R b f) =
    firstParamHom A B C F (compose A C E F Q R) τ b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleFirstLeft_element, chain_units_smul, chain_units_smul]
  have hL := associatorValueComponent_element A B C E F P' Q R b c e f
    (i := p + i) (l := k + r) (n := n) t q
    ((((Bimodule.paramValue A B C τ b c).f p x).v s (p + s) (by omega)) v)
    (by omega) rfl (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR, tripleFirstRight_element]
  rw [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

lemma associator_middleParam_value (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (R : Bimodule A E F) (τ : BimoduleParamTrans A C E K Q Q') (b : B) (f : F) :
    firstParamHom A B E F R (secondParam A B C E P τ) b f ≫
      homPostcompose _ (associatorValueHom A B C E F P Q' R b f) =
    secondParamHom A B C F P (firstParam A C E F R τ) b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleMiddleLeft_element, chain_units_smul]
  have hL := associatorValueComponent_element A B C E F P Q' R b c e f
    (i := p + i) (l := p + (k + r)) (n := n) t
    ((((Bimodule.paramValue A C E τ c e).f p x).v r (p + r) (by omega)) q) v
    (by omega) (by omega) (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR,
    tripleMiddleRight_element]

lemma associator_lastParam_value (P : Bimodule A B C) (Q : Bimodule A C E)
    {R R' : Bimodule A E F} (τ : BimoduleParamTrans A E F K R R') (b : B) (f : F) :
    secondParamHom A B E F (compose A B C E P Q) τ b f ≫
      homPostcompose _ (associatorValueHom A B C E F P Q R' b f) =
    secondParamHom A B C F P (secondParam A C E F Q τ) b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleLastLeft_element]
  have hL := associatorValueComponent_element A B C E F P Q R' b c e f
    (i := i) (l := p + (k + r)) (n := n)
    ((((Bimodule.paramValue A E F τ e f).f p x).v k (p + k) (by omega)) t) q v
    hi (by omega) (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR, tripleLastRight_element]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorParameterValues

/-! ## AssociatorParameters（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorParameters.lean） -/

/-! # 主Hom endにおける結合比較の三変数の任意パラメータ自然性 -/

@[expose] public section AssociatorParameters

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A}

/-- P変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_firstParam {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P') (f : F) :
    (firstParam A B E F R (firstParam A B C E Q τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P' Q) R).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P' Q R f).hom =
    (firstParam A B C F (compose A C E F Q R) τ).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (firstParam A B E F R (firstParam A B C E Q τ))
    (firstParam A B C F (compose A C E F Q R) τ)
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P' Q R d).hom)
  intro b d
  simp only [firstParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_firstParam_value A B C E F Q R τ b d

/-- Q変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_middleParam (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (R : Bimodule A E F) (τ : BimoduleParamTrans A C E K Q Q') (f : F) :
    (firstParam A B E F R (secondParam A B C E P τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q') R).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q' R f).hom =
    (secondParam A B C F P (firstParam A C E F R τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (firstParam A B E F R (secondParam A B C E P τ))
    (secondParam A B C F P (firstParam A C E F R τ))
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P Q' R d).hom)
  intro b d
  simp only [firstParam_value, secondParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_middleParam_value A B C E F P R τ b d

/-- R変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_lastParam (P : Bimodule A B C) (Q : Bimodule A C E)
    {R R' : Bimodule A E F} (τ : BimoduleParamTrans A E F K R R') (f : F) :
    (secondParam A B E F (compose A B C E P Q) τ).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q) R').rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R' f).hom =
    (secondParam A B C F P (secondParam A C E F Q τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (secondParam A B E F (compose A B C E P Q) τ)
    (secondParam A B C F P (secondParam A C E F Q τ))
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P Q R' d).hom)
  intro b d
  simp only [secondParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_lastParam_value A B C E F P Q τ b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorParameters
