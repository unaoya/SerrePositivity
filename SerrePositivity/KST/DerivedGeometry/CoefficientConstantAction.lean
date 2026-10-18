module

public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientAction

/-!
# 係数の定数作用の構造層加群上の自己準同型

概要：係数 h ∈ H の作用を、係数加群層を忘れた O 加群層の自己準同型として構成する。
方針：定数切断の自然性と構造層の中心性を使う。
規約：H の元同士の可換性は要求しない。
使われ方：KST D4・T1′、Toën Derived Azumaya §3.2 のアフィン係数作用の再構成。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤)) (M : (tensorCoefficientSheaf H a).Modules)

/--
概要：係数 h の定数作用は基礎加法群の前層の自己準同型になる。
方針：係数加群の制限の半線形性と定数切断の自然性を使う。
規約：任意の係数加群層を扱い、準連接性は仮定しない。
使われ方：KST D4、Toën §3.2 の定数係数作用。
-/
def coefficientConstantSmulPresheaf (h : H) : M.val.presheaf ⟶ M.val.presheaf where
  app U := AddCommGrpCat.ofHom {
    toFun m := ((tensorCoefficientConstant H a).app U h) • m
    map_zero' := smul_zero _
    map_add' := smul_add _ }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    change ((tensorCoefficientConstant H a).app V h) • M.val.map i m =
      M.val.map i (((tensorCoefficientConstant H a).app U h) • m)
    rw [M.val.map_smul]
    congr 1
    exact NatTrans.naturality_apply (tensorCoefficientConstant H a) i h

/--
概要：係数 h の定数作用は基礎 O 加群層の自己準同型になる。
方針：構造層の切断の像が中心的であることから O 線形性を示す。
規約：非可換 H に対しても定義する。
使われ方：KST D4・T1′、Toën §3.2 の大域切断からの係数作用の再構成。
-/
def coefficientConstantAction (h : H) :
    (tensorCoefficientSheaf H a).forget.obj M ⟶ (tensorCoefficientSheaf H a).forget.obj M where
  val := PresheafOfModules.homMk (coefficientConstantSmulPresheaf H a M h)
    (fun U r m => by
      change M.val.obj U at m
      change ((tensorCoefficientConstant H a).app U h) •
          (((tensorCoefficientSheaf H a).structureMap.hom).app U r • m) =
        ((tensorCoefficientSheaf H a).structureMap.hom).app U r •
          (((tensorCoefficientConstant H a).app U h) • m)
      rw [← mul_smul, ← mul_smul]
      exact congrArg (fun b : (tensorCoefficientSheaf H a).ring.obj.obj U => b • m)
        (tensorCoefficientSheaf_structureMap_commutes H a U.unop r
          ((tensorCoefficientConstant H a).app U h)).eq.symm)

/--
概要：構成した自己準同型の切断上の値は h の定数切断による作用。
方針：前層射の構成を展開する。
規約：すべての開集合上での式。
使われ方：KST D4、Toën §3.2 の大域切断の計算。
-/
lemma coefficientConstantAction_apply (h : H) (U : X.Opens) (m : M.val.obj (.op U)) :
    ((coefficientConstantAction H a M h).val.app (.op U)).hom m =
      ((tensorCoefficientConstant H a).app (.op U) h) • m := rfl

/--
概要：定数作用の自己準同型は H の加法を保つ。
方針：切断ごとに定数切断の加法性と加群の分配則を使う。
規約：基礎 O 加群層の射の加法について述べる。
使われ方：KST D4、Toën §3.2 の係数環の作用の再構成。
-/
lemma coefficientConstantAction_add (h k : H) :
    coefficientConstantAction H a M (h + k) =
      coefficientConstantAction H a M h + coefficientConstantAction H a M k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj U at m
  change ((tensorCoefficientConstant H a).app U (h + k)) • m =
    ((tensorCoefficientConstant H a).app U h) • m + ((tensorCoefficientConstant H a).app U k) • m
  rw [map_add, add_smul]

/--
概要：h k の定数作用は k の作用の後に h の作用を施すことに等しい。
方針：定数切断の乗法性と左加群の作用の結合則を使う。
規約：圏の射の合成順序を明示して非可換性を保つ。
使われ方：KST D4、Toën §3.2 の H 作用の再構成。
-/
lemma coefficientConstantAction_mul (h k : H) :
    coefficientConstantAction H a M (h * k) =
      coefficientConstantAction H a M k ≫ coefficientConstantAction H a M h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj U at m
  change ((tensorCoefficientConstant H a).app U (h * k)) • m =
    ((tensorCoefficientConstant H a).app U h) • (((tensorCoefficientConstant H a).app U k) • m)
  rw [map_mul, mul_smul]

/--
概要：係数 0 の定数作用は零射。
方針：切断上で定数切断の零と零スカラーの作用を計算する。
規約：基礎 O 加群層の零射を使う。
使われ方：KST D4、Toën §3.2 の係数の環作用。
-/
lemma coefficientConstantAction_zero : coefficientConstantAction H a M 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj U at m
  change ((tensorCoefficientConstant H a).app U 0) • m = 0
  rw [map_zero, zero_smul]

/--
概要：係数 1 の定数作用は恒等射。
方針：切断上で単位元の作用を計算する。
規約：単位的な左加群の規約に従う。
使われ方：KST D4、Toën §3.2 の係数の環作用。
-/
lemma coefficientConstantAction_one : coefficientConstantAction H a M 1 = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj U at m
  change ((tensorCoefficientConstant H a).app U 1) • m = m
  rw [map_one, one_smul]

/--
概要：定数係数の作用を基礎 O 加群層の自己準同型環への環準同型とする。
方針：証明した零・単位・加法・乗法の法則を束ねる。
規約：自己準同型環の積は左作用に対応する射の逆順の合成。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数作用の再構成。
-/
def coefficientConstantActionRingHom :
    H →+* End ((tensorCoefficientSheaf H a).forget.obj M) where
  toFun h := End.of (coefficientConstantAction H a M h)
  map_zero' := by apply End.ext; exact coefficientConstantAction_zero H a M
  map_one' := by apply End.ext; exact coefficientConstantAction_one H a M
  map_add' h k := by apply End.ext; exact coefficientConstantAction_add H a M h k
  map_mul' h k := by apply End.ext; exact coefficientConstantAction_mul H a M h k

/--
概要：定数係数の作用は係数加群層の射について自然。
方針：各開で係数線形な射が定数切断の作用を保つことを使う。
規約：忘却関手の自然自己変換として述べる。
使われ方：KST D4・T1′、Toën §3.2 の係数線形性の再構成。
-/
def coefficientConstantActionNat (h : H) :
    (tensorCoefficientSheaf H a).forget ⟶ (tensorCoefficientSheaf H a).forget where
  app M := coefficientConstantAction H a M h
  naturality {M N} φ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M.val.obj U at m
    change ((tensorCoefficientConstant H a).app U h) • (φ.val.app U m) =
      φ.val.app U (((tensorCoefficientConstant H a).app U h) • m)
    exact ((φ.val.app U).hom.map_smul ((tensorCoefficientConstant H a).app U h) m).symm

end SerrePositivity.KST.DerivedGeometry
