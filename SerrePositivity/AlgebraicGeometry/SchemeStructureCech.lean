module

public import SerrePositivity.AlgebraicGeometry.SchemeModuleCechRefinement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
概要：構造層を準連接係数の Čech 比較の入口に置く。
方針：一つの生成元の自由な構造層加群を用いて準連接性を示す。
規約：切断の加法群・乗法は元の構造層のもの。
使われ方：Proj の構造層の標準開計算と、共通アフィン細分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

/-- 構造層を、それ自身の上の階数一の加群として扱う。 -/
abbrev schemeStructureModule (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

/-- 構造層加群は準連接。 -/
instance schemeStructureModuleQuasicoherent (Y : Scheme.{u}) :
    (schemeStructureModule Y).IsQuasicoherent := by
  let F := SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} PUnit)
  haveI : F.IsQuasicoherent := by dsimp only [F]; infer_instance
  let e : F ≅ schemeStructureModule Y :=
    coproductUniqueIso (fun _ : ULift.{u} PUnit ↦ schemeStructureModule Y)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e inferInstance

/-- 構造層の切断を大域切断の環上で扱う、実際の係数前層。 -/
abbrev schemeStructureCechPresheaf (Y : Scheme.{u}) :=
  schemeModuleCechPresheaf (schemeStructureModule Y)

/-- 構造層の切断の大域スカラー作用は、制限した切断の乗法。 -/
theorem schemeStructureCechPresheaf_smul (Y : Scheme.{u}) (U : Y.Opens)
    (r : Γ(Y, ⊤)) (x : (schemeStructureCechPresheaf Y).obj (op U)) :
    r • x = @HMul.hMul Γ(Y, U) Γ(Y, U) Γ(Y, U) inferInstance
      ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r) x :=
  rfl

/-- 構造層のアフィン被覆の細分は、実際の Čech H の同型を誘導する。
原典 Stacks 30.2.6 のアフィン被覆の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructureCechRefinement_homologyMap_isIso (Y : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcover : (⨆ j, V j) = ⊤) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (openCoverCechRefinementMap (schemeStructureCechPresheaf Y) U V ρ hρ) q) :=
  schemeModuleCechRefinement_homologyMap_isIso (schemeStructureModule Y) U V ρ hρ hU hV hcover q

end SerrePositivity.AlgebraicGeometry
