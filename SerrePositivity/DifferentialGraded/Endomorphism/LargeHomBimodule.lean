module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomBimodule

/-! # 対象型のsmall性を仮定しない指定対象からのHom bimodule

End(E)の一対象型だけがsmallであればよい。YonedaのHom endを大きいD上に取らず、
代表加群のE成分を直接用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- Yoneda拡張のE成分は共変representable Hom(E,−)の全次数写像。 -/
lemma endomorphismYonedaApp (X Y : D) :
    yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) =
      (leftRepresentable A E).map X Y := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [yonedaExtensionApp_apply]
  change (p * r).negOnePow • forward A h f hn =
    leftAction A (leftRepresentable A E) f h hn
  exact (leftRepresentable_action A E X Y f h hn).symm

/-- 大きい対象型でも定義できる、右End(E)加群間の全次数自然族。 -/
def largeEndomorphismHomParam (X Y : D) :
    ModuleParamTrans A (EndomorphismObject E) (X ⟶[Complex A] Y)
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) where
  app _ := yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E)
  naturality x y := by
    change (β_ (X ⟶[Complex A] Y) (op E ⟶[Complex A] op E)).hom ≫
      ((𝟙 _ ≫ (representable A X).map (op E) (op E)) ⊗ₘ
        yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E)) ≫ enrichedComposition _ _ _ =
      (yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) ⊗ₘ
        (𝟙 _ ≫ (representable A Y).map (op E) (op E))) ≫ enrichedComposition _ _ _
    simp only [Category.id_comp]
    exact yonedaExtensionApp_naturality A X (representable A Y) (𝟙 _) (op E) (op E)

/-- 大きいDに対するHom(E,−)。Small Dを仮定せずに全Hom自然性を保つ。 -/
def largeEndomorphismHomBimodule : Bimodule A (EndomorphismObject E) D :=
  Bimodule.ofParamTrans A _ D (endomorphismHomRight A D E)
    (largeEndomorphismHomParam A D E)
    (by
      intro X b
      change eId (Complex A) X ≫ yonedaExtensionApp A X (representable A X) (𝟙 _) (op E) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable A E).map_id X)
    (by
      intro X Y Z b
      change eComp (Complex A) X Y Z ≫
        yonedaExtensionApp A X (representable A Z) (𝟙 _) (op E) =
        (yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) ⊗ₘ
          yonedaExtensionApp A Y (representable A Z) (𝟙 _) (op E)) ≫ enrichedComposition _ _ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable A E).map_comp X Y Z)

/-- smallな場合、既存Yoneda制限による構成と一致する。 -/
lemma largeEndomorphismHomBimodule_eq [Small.{u} D] :
    largeEndomorphismHomBimodule A D E = endomorphismHomBimodule A D E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (largeEndomorphismHomBimodule A D E).toFunctor)
    (G := (endomorphismHomBimodule A D E).toFunctor) (fun _ => rfl)
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  change (moduleHomEquiv A (EndomorphismObject E) _
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y)).symm
        (largeEndomorphismHomParam A D E X Y) ≫ moduleHomπ A _ _ _ b =
    (moduleHomEquiv A (EndomorphismObject E) _
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y)).symm
        (endomorphismHomParam A D E X Y) ≫ moduleHomπ A _ _ _ b
  rw [moduleHomEquiv_symm_π, moduleHomEquiv_symm_π]
  exact (yonedaHom_π A D X Y E).symm

end SerrePositivity.DifferentialGraded
