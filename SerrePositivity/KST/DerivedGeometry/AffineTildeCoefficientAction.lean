module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientFull
public import Mathlib.CategoryTheory.Endomorphism
public import SerrePositivity.KST.DerivedGeometry.StructureScalarAction

/-!
概要：左 H 加群の作用を通常の tilde 層の O 線形自己準同型へ移す。
方針：R 上の中心性から作用射を R 線形にし、tilde の加法的関手で環の法則を保つ。
規約：H の可換性・平坦性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群層の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：左 H の各元の作用は基礎 R 加群の自己準同型。
方針：基礎環の像が中心的であることと左加群の結合則を使う。
規約：射の合成順序は左作用に対応させる。
使われ方：KST D4・T1′、Toën §3.2 の tilde への作用の移送。
-/
def affineScalarEnd (M : ModuleCat.{u} H) (h : H) :
    End ((ModuleCat.restrictScalars (algebraMap R H)).obj M) := by
  letI : Module R M := Module.compHom M (algebraMap R H)
  exact End.of (ModuleCat.ofHom {
    toFun m := h • m
    map_add' m n := smul_add h m n
    map_smul' r m := by
      change h • (algebraMap R H r • m) = algebraMap R H r • (h • m)
      rw [← mul_smul, ← mul_smul]
      exact congrArg (fun k : H => k • m) (Algebra.commutes r h).symm })

/--
概要：左 H 作用を基礎 R 加群の自己準同型環への環準同型とする。
方針：各元の作用射に対して加群の零・単位・加法・積の法則を確認する。
規約：自己準同型環の積は左作用の順序に対応する。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数作用。
-/
def affineScalarEndRingHom (M : ModuleCat.{u} H) :
    H →+* End ((ModuleCat.restrictScalars (algebraMap R H)).obj M) where
  toFun h := affineScalarEnd H M h
  map_zero' := by
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change (0 : H) • m = 0
    exact zero_smul H m
  map_one' := by
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change (1 : H) • m = m
    exact one_smul H m
  map_add' h k := by
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change (h + k) • m = h • m + k • m
    exact add_smul h k m
  map_mul' h k := by
    apply End.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change (h * k) • m = h • (k • m)
    exact mul_smul h k m

/--
概要：通常の tilde 層に O 線形な左 H 作用を与える環準同型。
方針：基礎 R 加群の作用を tilde の加法的関手で移す。
規約：基礎 O 加群層は通常の tilde を保持する。
使われ方：KST D4・T1′、Toën §3.2 の係数加群層の本質的全射性。
-/
def affineTildeActionRingHom (M : ModuleCat.{u} H) :
    H →+* End (tilde ((ModuleCat.restrictScalars (algebraMap R H)).obj M)) where
  __ := (CategoryTheory.Functor.mapEnd
    ((ModuleCat.restrictScalars (algebraMap R H)).obj M) (tilde.functor R)).comp
      (affineScalarEndRingHom (R := R) H M).toMonoidHom
  map_zero' := by
    apply End.ext
    change tilde.map ((affineScalarEndRingHom H M) 0).asHom = 0
    rw [map_zero]
    exact (tilde.functor R).map_zero _ _
  map_add' h k := by
    apply End.ext
    change tilde.map ((affineScalarEndRingHom H M) (h + k)).asHom =
      tilde.map ((affineScalarEndRingHom H M) h).asHom +
        tilde.map ((affineScalarEndRingHom H M) k).asHom
    rw [map_add]
    exact (tilde.functor R).map_add

/--
概要：基礎 R 加群の左 H 作用は H 線形写像に関して自然。
方針：元の H 加群の線形性を各元に適用する。
規約：O 加群層へ移す前の同じ作用射を使う。
使われ方：KST D4・T1′、Toën §3.2 の係数 tilde 関手。
-/
theorem affineScalarEnd_naturality {M N : ModuleCat.{u} H} (f : M ⟶ N) (h : H) :
    (affineScalarEnd H M h).asHom ≫ (ModuleCat.restrictScalars (algebraMap R H)).map f =
      (ModuleCat.restrictScalars (algebraMap R H)).map f ≫ (affineScalarEnd H N h).asHom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M at m
  change f.hom (h • m) = h • f.hom m
  exact f.hom.map_smul h m

/--
概要：tilde 層に移した左 H 作用は元の H 線形写像に関して自然。
方針：基礎 R 加群の可換な式を同じ tilde 関手で送る。
規約：層の切断ごとの独立な作用を選ばない。
使われ方：KST D4・T1′、Toën §3.2 の係数層化の関手性。
-/
theorem affineTildeAction_naturality {M N : ModuleCat.{u} H} (f : M ⟶ N) (h : H) :
    ((affineTildeActionRingHom H M) h).asHom ≫
        tilde.map ((ModuleCat.restrictScalars (algebraMap R H)).map f) =
      tilde.map ((ModuleCat.restrictScalars (algebraMap R H)).map f) ≫
        ((affineTildeActionRingHom H N) h).asHom :=
  ((tilde.functor R).map_comp _ _).symm.trans
    ((congrArg (tilde.functor R).map (affineScalarEnd_naturality H f h)).trans
      ((tilde.functor R).map_comp _ _))

/--
概要：通常の tilde の大域切断の単位同型は H の各作用射と可換。
方針：単位自然同型の自然性を基礎 R 加群の H 作用に適用する。
規約：係数 tilde の大域切断の H 線形性に同じ単位を使う。
使われ方：KST D4・T1′、Toën §3.2 のアフィン比較の本質的全射性。
-/
theorem affineTildeAction_unit (M : ModuleCat.{u} H) (h : H) :
    (affineScalarEnd H M h).asHom ≫
        (tilde.toTildeΓNatIso (R := R)).hom.app
          ((ModuleCat.restrictScalars (algebraMap R H)).obj M) =
      (tilde.toTildeΓNatIso (R := R)).hom.app
          ((ModuleCat.restrictScalars (algebraMap R H)).obj M) ≫
        moduleSpecΓFunctor.map ((affineTildeActionRingHom H M) h).asHom :=
  (tilde.toTildeΓNatIso (R := R)).hom.naturality (affineScalarEnd H M h).asHom

/--
概要：tilde 層へ移した H 作用は基礎環 R 上で構造層の作用に一致する。
方針：準連接 tilde 層の大域切断の忠実性と、単位同型の自然性・R 線形性を使う。
規約：平坦性や H の可換性を要求しない。
使われ方：KST D4・T1′、Toën §3.2 のテンソル係数環の作用の構成。
-/
theorem affineTildeAction_base (M : ModuleCat.{u} H) (r : R) :
    ((affineTildeActionRingHom H M) (algebraMap R H r)).asHom =
      structureScalarAction (Scheme.ΓSpecIso R).inv.hom
        (tilde ((ModuleCat.restrictScalars (algebraMap R H)).obj M)) r := by
  let V := (ModuleCat.restrictScalars (algebraMap R H)).obj M
  let e : V ≅ moduleSpecΓFunctor.obj (tilde V) := (tilde.toTildeΓNatIso (R := R)).app V
  apply affineUnderlyingHom_ext
  apply (cancel_epi e.hom).mp
  have hs : (affineScalarEnd H M (algebraMap R H r)).asHom ≫ e.hom =
      e.hom ≫ moduleSpecΓFunctor.map
        (structureScalarAction (Scheme.ΓSpecIso R).inv.hom (tilde V) r) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change e.hom.hom (r • m) =
      sectionBaseMap (Scheme.ΓSpecIso R).inv.hom ⊤ r •
        (show (tilde V).val.obj (.op ⊤) from e.hom.hom m)
    have hr : sectionBaseMap (Scheme.ΓSpecIso R).inv.hom ⊤ r =
        (Scheme.ΓSpecIso R).inv.hom r := by
      simp [sectionBaseMap]
    rw [hr]
    exact e.hom.hom.map_smul r m
  exact (affineTildeAction_unit H M (algebraMap R H r)).symm.trans hs

end SerrePositivity.KST.DerivedGeometry
