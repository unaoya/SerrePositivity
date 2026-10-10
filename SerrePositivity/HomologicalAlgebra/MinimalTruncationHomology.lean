module

public import SerrePositivity.HomologicalAlgebra.KoszulTruncation
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.MinimalTruncation

/-! # 極小分解の切り詰めと係数変更後の Tor

下端を除く次数では、任意の加法関手を施した切り詰めのホモロジーは分解全体と一致する。
特に係数変更の平坦性を仮定せず Tor を計算できる。下端の次数はこの同型の範囲に含めない。
-/

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory

namespace SerrePositivity.MinimalFreeResolution

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (M : FGModuleCat.{u} R) (l : ℕ)

/-- 切り詰めの下端より上では、任意の加法関手を施したホモロジーが一致する。 -/
noncomputable def truncatedMapHomologyIso {D : Type w} [Category.{v} D] [Abelian D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive] (i : ℕ) (hi : i < l) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (truncated M l)).homology (-(i : ℤ)) ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj (extRes (resolution M))).homology (-(i : ℤ)) :=
  StupidTruncation.mapHomologyIso F _ _ _ (by omega)

/-- 係数変更した切り詰めは、下端より上で代数係数の Tor を計算する。 -/
noncomputable def truncatedTorAlgIso {S : Type u} [CommRing S] (φ : R →+* S)
    (i : ℕ) (hi : i < l) :
    ModuleCat.of S (TorAlg φ i M) ≅ (baseChange φ (truncated M l)).homology (-(i : ℤ)) :=
  torIsoCochain φ (isResolutionOf_extRes (resolution M)) i ≪≫
    (truncatedMapHomologyIso M l (ModuleCat.extendScalars φ) i hi).symm

/-- 任意の加群係数について、第2変数の極小分解で通常の Tor を計算する。 -/
noncomputable def truncatedTorModuleIso (N : ModuleCat.{u} R) (i : ℕ) (hi : i < l) :
    ModuleCat.of R (TorModule R i N M) ≅
      (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (truncated M l)).homology (-(i : ℤ)) :=
  torModuleIsoCochain N (isResolutionOf_extRes (resolution M)) i ≪≫
    (truncatedMapHomologyIso M l (tensorLeft N) i hi).symm

/-- 第1変数の極小分解を切り詰めても、下端より上で通常の Tor を計算できる。 -/
noncomputable def truncatedTorModuleLeftIso (N : ModuleCat.{u} R) (i : ℕ) (hi : i < l) :
    ModuleCat.of R (TorModule R i M N) ≅
      (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (truncated M l)).homology (-(i : ℤ)) :=
  (torModuleComm i M N).toModuleIso ≪≫ truncatedTorModuleIso M l N i hi

/-- Koszul 構成後も、切り詰めの下端より上では分解全体と同じホモロジーをもつ。 -/
noncomputable def truncatedKoszulMapHomologyIso {S : Type u} [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] {e : ℕ} (x : Fin e → S)
    (i : ℕ) (hi : i < l) :
    (koszulComplexOn x ((F.mapHomologicalComplex (.up ℤ)).obj (truncated M l))).homology
      (-(i : ℤ)) ≅
    (koszulComplexOn x ((F.mapHomologicalComplex (.up ℤ)).obj
      (extRes (resolution M)))).homology (-(i : ℤ)) :=
  StupidTruncation.koszulMapHomologyIso F x _ _ _ (by omega)

end SerrePositivity.MinimalFreeResolution
