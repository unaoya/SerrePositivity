module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.BaseSections

/-!
概要：基礎環の各元を構造層加群の自己準同型として作用させる。
方針：構造層への切断を各開へ制限し、可換環上の線形性と前層の自然性を使う。
規約：作用を実際の射として指定し、暗黙の新しい線形構造を加えない。
使われ方：KST D4・T1′、Toën §3.2 の係数 tilde の基礎環との両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A] {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：基礎環の切断による作用は加法群の前層の自己準同型。
方針：作用の切断の制限と加群の半線形な制限写像の両立を使う。
規約：全ての構造層加群を扱う。
使われ方：KST D4、Toën §3.2 の基礎環の作用。
-/
def structureScalarPresheaf (M : X.Modules) (r : A) : M.val.presheaf ⟶ M.val.presheaf where
  app U := AddCommGrpCat.ofHom {
    toFun (m : M.val.obj U) :=
      (show X.ringCatSheaf.obj.obj U from sectionBaseMap a U.unop r) • m
    map_zero' := smul_zero _
    map_add' := smul_add _ }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    change M.val.obj U at m
    change (show X.ringCatSheaf.obj.obj V from sectionBaseMap a V.unop r) •
        (show M.val.obj V from M.val.map i m) =
      M.val.map i ((show X.ringCatSheaf.obj.obj U from sectionBaseMap a U.unop r) • m)
    rw [M.val.map_smul]
    congr 1
    exact (congrArg (fun f : A →+* Γ(X, V.unop) => f r)
      (restriction_comp_sectionBaseMap a i.unop)).symm

/--
概要：基礎環の各元の作用は構造層加群の自己準同型。
方針：構造層の各切断環の可換性から作用の線形性を示す。
規約：切断上での作用を保持する。
使われ方：KST D4・T1′、Toën §3.2 の係数作用との基礎環の一致。
-/
def structureScalarAction (M : X.Modules) (r : A) : M ⟶ M where
  val := PresheafOfModules.homMk (structureScalarPresheaf a M r)
    (fun U s m => by
      letI : CommRing (X.ringCatSheaf.obj.obj U) :=
        inferInstanceAs (CommRing Γ(X, U.unop))
      change (show X.ringCatSheaf.obj.obj U from sectionBaseMap a U.unop r) • (s • m) =
        s • ((show X.ringCatSheaf.obj.obj U from sectionBaseMap a U.unop r) • m)
      exact smul_comm _ _ _)

/--
概要：構造層加群の基礎環作用の切断上の値を計算する。
方針：構成した作用射の成分を読む。
規約：同じ制限した基礎環の切断を使う。
使われ方：KST D4、Toën §3.2 の基礎環との両立の成分計算。
-/
theorem structureScalarAction_apply (M : X.Modules) (r : A) (U : X.Opens)
    (m : M.val.obj (.op U)) :
    (structureScalarAction a M r).val.app (.op U) m = sectionBaseMap a U r • m := rfl

/--
概要：構造層加群の基礎環作用は O 線形な射に関して自然。
方針：各開の線形性を制限した基礎環の切断へ適用する。
規約：元の層の射を変更しない。
使われ方：KST D4・T1′、Toën §3.2 の作用の移送。
-/
theorem structureScalarAction_naturality {M N : X.Modules} (f : M ⟶ N) (r : A) :
    structureScalarAction a M r ≫ f = f ≫ structureScalarAction a N r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (f.val.app U).hom.map_smul (sectionBaseMap a U.unop r) m

end SerrePositivity.KST.DerivedGeometry
