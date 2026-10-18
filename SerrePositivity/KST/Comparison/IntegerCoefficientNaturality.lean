module

public import SerrePositivity.KST.Comparison.IntegerCoefficientComparison
public import SerrePositivity.KST.Comparison.HomologyHomotopy

/-!
# 局所係数から整数係数への比較の自然性

概要：全ての局所係数のホモロジー同型は整数ホモロジー同型を含む。
方針：Kan 拡張の単位で比較の可換性を示し、正規化とホモロジーへ渡す。
規約：Weibel K-book IV.1.6。ホモトピーファイバーの acyclic 性との同値は別工程。
使われ方：plus のホモロジー同型の整数係数での帰結。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

/--
概要：局所係数の誘導写像と Kan 拡張の単位は可換である。
方針：源の Kan 拡張の因子分解式を評価する。
規約：引き戻し係数から標的の係数への写像。
使われ方：整数比較の自然性。
-/
@[reassoc] theorem localCoefficientSimplicialMap_unit {X Y : SSet.{u}}
    (f : X ⟶ Y) (L : LocalCoefficientSystem Y) (e : X.Elements) :
    ((Functor.Elements.π X).leftKanExtensionUnit
      (pullbackLocalCoefficients f L).coefficients).app e ≫
        (localCoefficientSimplicialMap f L).app e.obj =
      ((Functor.Elements.π Y).leftKanExtensionUnit L.coefficients).app (f.mapElements.obj e) :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ e

/--
概要：局所係数の誘導写像と自由整数単体的群の誘導写像は整数比較に関して可換である。
方針：源の左 Kan 拡張の普遍性で各単体の生成元に帰着する。
規約：全ての単体写像。
使われ方：整数局所係数ホモロジー比較の自然性。
-/
theorem integerCoefficientComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    localCoefficientSimplicialMap f (constantLocalCoefficients Y integerCoefficientGroup) ≫
      integerCoefficientComparison Y =
    integerCoefficientComparison X ≫ freeAbelianSimplicialFunctor.map f := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X)
    (constantLocalCoefficients X integerCoefficientGroup).coefficients
  apply NatTrans.ext
  funext e
  change ((Functor.Elements.π X).leftKanExtensionUnit
      (constantLocalCoefficients X integerCoefficientGroup).coefficients).app e ≫
        ((localCoefficientSimplicialMap f
          (constantLocalCoefficients Y integerCoefficientGroup)).app e.obj ≫
        (integerCoefficientComparison Y).app e.obj) =
    ((Functor.Elements.π X).leftKanExtensionUnit
      (constantLocalCoefficients X integerCoefficientGroup).coefficients).app e ≫
        ((integerCoefficientComparison X).app e.obj ≫
        (freeAbelianSimplicialFunctor.map f).app e.obj)
  let ηX := ((Functor.Elements.π X).leftKanExtensionUnit
    (constantLocalCoefficients X integerCoefficientGroup).coefficients).app e
  let ηY := ((Functor.Elements.π Y).leftKanExtensionUnit
    (constantLocalCoefficients Y integerCoefficientGroup).coefficients).app (f.mapElements.obj e)
  let m := (localCoefficientSimplicialMap f
    (constantLocalCoefficients Y integerCoefficientGroup)).app e.obj
  let cX := (integerCoefficientComparison X).app e.obj
  let cY := (integerCoefficientComparison Y).app e.obj
  let Ff := (freeAbelianSimplicialFunctor.map f).app e.obj
  have hm : ηX ≫ m = ηY := localCoefficientSimplicialMap_unit f _ e
  have hcX : ηX ≫ cX = integerGeneratorMap e.val := integerCoefficientComparison_unit X e
  have hcY : ηY ≫ cY = integerGeneratorMap (f.app e.obj e.val) :=
    integerCoefficientComparison_unit Y (f.mapElements.obj e)
  have hgen : integerGeneratorMap (f.app e.obj e.val) = integerGeneratorMap e.val ≫ Ff := by
    change AddCommGrpCat.free.map (↾fun _ => f.app e.obj e.val) =
      AddCommGrpCat.free.map (↾fun _ => e.val) ≫ AddCommGrpCat.free.map (f.app e.obj)
    rw [← AddCommGrpCat.free.map_comp]
    rfl
  exact calc
    ηX ≫ (m ≫ cY) = (ηX ≫ m) ≫ cY := (Category.assoc _ _ _).symm
    _ = ηY ≫ cY := congrArg (fun q => q ≫ cY) hm
    _ = integerGeneratorMap (f.app e.obj e.val) := hcY
    _ = integerGeneratorMap e.val ≫ Ff := hgen
    _ = (ηX ≫ cX) ≫ Ff := congrArg (fun q => q ≫ Ff) hcX.symm
    _ = ηX ≫ (cX ≫ Ff) := Category.assoc _ _ _

/--
概要：正規化整数比較と単体写像の誘導鎖写像は可換である。
方針：単体的アーベル群での可換性に正規化関手を施す。
規約：源の引き戻し定数整数係数は定数整数係数と一致する。
使われ方：ホモロジーの比較写像の自然性。
-/
theorem integerLocalCoefficientChainsIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    localCoefficientChainsMap f (constantLocalCoefficients Y integerCoefficientGroup) ≫
      (integerLocalCoefficientChainsIso Y).hom =
    (integerLocalCoefficientChainsIso X).hom ≫ normalizedIntegralChains.map f := by
  change (normalizedMooreComplex _).map
      (localCoefficientSimplicialMap f (constantLocalCoefficients Y integerCoefficientGroup)) ≫
        (normalizedMooreComplex _).map (integerCoefficientComparison Y) =
    (normalizedMooreComplex _).map (integerCoefficientComparison X) ≫
      (normalizedMooreComplex _).map (freeAbelianSimplicialFunctor.map f)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    integerCoefficientComparison_naturality]

/--
概要：整数局所係数ホモロジーの比較は単体写像に関して自然である。
方針：正規化鎖写像の可換性にホモロジーを施す。
規約：全自然数次数。
使われ方：整数係数のホモロジー同型の帰結。
-/
theorem integerLocalCoefficientHomologyIso_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    localCoefficientHomologyMap f (constantLocalCoefficients Y integerCoefficientGroup) n ≫
      (integerLocalCoefficientHomologyIso Y n).hom =
    (integerLocalCoefficientHomologyIso X n).hom ≫ integralHomologyMap f n := by
  change HomologicalComplex.homologyMap
      (localCoefficientChainsMap f (constantLocalCoefficients Y integerCoefficientGroup)) n ≫
        HomologicalComplex.homologyMap (integerLocalCoefficientChainsIso Y).hom n =
    HomologicalComplex.homologyMap (integerLocalCoefficientChainsIso X).hom n ≫
      HomologicalComplex.homologyMap (normalizedIntegralChains.map f) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    integerLocalCoefficientChainsIso_naturality]

/--
概要：全局所係数のホモロジー同型は整数ホモロジー同型を誘導する。
方針：定数整数係数へ適用し、構成した比較同型の自然性で移す。
規約：局所係数の条件を整数係数だけに弱めない。
使われ方：plus の acyclic 性からの整数ホモロジー同型。
-/
theorem integralHomologyIsomorphism_of_local {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : LocalHomologyIsomorphism f) : IntegralHomologyIsomorphism f := by
  intro n
  have : IsIso (localCoefficientHomologyMap f
      (constantLocalCoefficients Y integerCoefficientGroup) n) := hf _ n
  have h : integralHomologyMap f n = (integerLocalCoefficientHomologyIso X n).inv ≫
      localCoefficientHomologyMap f (constantLocalCoefficients Y integerCoefficientGroup) n ≫
        (integerLocalCoefficientHomologyIso Y n).hom := by
    rw [integerLocalCoefficientHomologyIso_naturality, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end SerrePositivity.KST.Comparison
