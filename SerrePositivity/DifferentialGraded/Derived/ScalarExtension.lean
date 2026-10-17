module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionHomotopy

/-! # 任意の環準同型による導来係数拡大

全 dg 自然な射影解像度を K(D) へ取り、係数変更後の主導来圏へ送る。
係数環の flatness も元の dg 圏の local flatness も要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定した射影解像度族による非 flat な導来係数拡大。 -/
def resolutionDerivedExtension
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ D) :=
  moduleDerivedResolutionFunctor A D R ⋙ moduleExtensionHomotopyToDerived φ D

/-- 標準 semifree 解像度による導来係数拡大。 -/
def derivedExtension :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ D) :=
  resolutionDerivedExtension φ D (moduleCanonicalProjectiveResolution A D)

/-- 指定解像度による実際の計算式。 -/
def resolutionDerivedExtensionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (resolutionDerivedExtension φ D R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj (R M).obj) :=
  (moduleExtensionHomotopyToDerived φ D).mapIso (moduleDerivedResolutionComputation A D R M)

/-- 解像度選択の変更は自然同型を与える。 -/
def resolutionDerivedExtensionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtension φ D R ≅ resolutionDerivedExtension φ D S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (moduleExtensionHomotopyToDerived φ D)

lemma resolutionDerivedExtensionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtensionIso φ D R R = Iso.refl _ := by
  unfold resolutionDerivedExtensionIso
  rw [moduleDerivedResolutionIso_self]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (moduleExtensionHomotopyToDerived φ D).map_id _

lemma resolutionDerivedExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtensionIso φ D R S ≪≫ resolutionDerivedExtensionIso φ D S T =
      resolutionDerivedExtensionIso φ D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (moduleExtensionHomotopyToDerived φ D).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (moduleExtensionHomotopyToDerived φ D).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (moduleExtensionHomotopyToDerived φ D).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 任意の証明付き射影解像度で標準導来係数拡大を計算できる。 -/
def derivedExtensionResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (derivedExtension φ D).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj P.obj) := by
  let R := moduleCanonicalProjectiveResolution A D
  exact resolutionDerivedExtensionComputation φ D R M ≪≫
    (moduleExtensionHomotopyToDerived φ D).mapIso
      (@asIso _ _ _ _ ((moduleToHomotopy A D).map ((R M).comparison P))
        ((R M).comparison_isIso_homotopy P))

/-- underived 比較射。これを同型とするには増大射の係数変更後の擬同型性が必要。 -/
def derivedExtensionComparison {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (derivedExtension φ D).obj ((moduleToDerived A D).obj M) ⟶
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj M) :=
  (derivedExtensionResolutionComputation φ D P).hom ≫
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map P.π)

/-- 増大射が係数変更後も擬同型なら underived 比較は同型。 -/
lemma derivedExtensionComparison_isIso {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (hπ : moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map P.π)) :
    IsIso (derivedExtensionComparison φ D P) := by
  have := moduleToDerived_inverts A' (DGBaseChange φ D) _ hπ
  unfold derivedExtensionComparison
  infer_instance

end SerrePositivity.DifferentialGraded.ScalarExtension
