module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NativeCoproduct
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorInclusions
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCoconeLegs

/-!
# 指定 native 余積錐の二脚と厳密なテンソル比較

概要：HA 3.2.4.7 の指定余積錐の脚を元の厳密包含へ同定する。
方針：再添字した脚を同じ離散頂点へ戻し、余積からの指定射の式を使う。
規約：余錐も比較も既存の指定されたものを使い、対象ごとの同型に置き換えない。
使われ方：coproduct_tensor の二脚の条件を実例で検証するための厳密な照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CAlgSimplicialCategory A)

/-- 採用した native な余錐の第一脚は、元の cofibrant な余積の第一包含。 -/
lemma cAlgNativeCoprodCocone_leg_left :
    coherentCoconeLegMap (cAlgNativeCoprodCocone A X Y) binaryPointLeft =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKCoprodInl A X Y))).edge := by
  rw [cAlgNativeCoprodCocone, coherentCoconeLegMap_ofDiagramEq]
  change coherentCoconeLegMap
    ((strictNativeCocone (cAlgBinaryCocone A X Y)).restrict cAlgBinaryShapeIso.hom)
      binaryPointLeft = _
  rw [coherentCoconeLegMap_restrict]
  change coherentCoconeLegMap (strictNativeCocone (cAlgBinaryCocone A X Y))
    (coprod.inl ≫ cAlgBinaryShapeIso.hom) = _
  rw [cAlgBinaryShapeIso_left]
  exact strictNativeCoconeLeg_eq (cAlgBinaryCocone A X Y) ⟨⟨true⟩⟩

/-- 採用した native な余錐の第二脚は、元の cofibrant な余積の第二包含。 -/
lemma cAlgNativeCoprodCocone_leg_right :
    coherentCoconeLegMap (cAlgNativeCoprodCocone A X Y) binaryPointRight =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKCoprodInr A X Y))).edge := by
  rw [cAlgNativeCoprodCocone, coherentCoconeLegMap_ofDiagramEq]
  change coherentCoconeLegMap
    ((strictNativeCocone (cAlgBinaryCocone A X Y)).restrict cAlgBinaryShapeIso.hom)
      binaryPointRight = _
  rw [coherentCoconeLegMap_restrict]
  change coherentCoconeLegMap (strictNativeCocone (cAlgBinaryCocone A X Y))
    (coprod.inr ≫ cAlgBinaryShapeIso.hom) = _
  rw [cAlgBinaryShapeIso_right]
  exact strictNativeCoconeLeg_eq (cAlgBinaryCocone A X Y) ⟨⟨false⟩⟩

/-- 界面へ供給した余極限錐の第一脚も、同じ第一包含の区間全体。 -/
lemma barrattEcclesCoprodWith_cocone_leg_left (x y : (CAlg_R A) _⦋0⦌) :
    coherentCoconeLegMap (barrattEcclesCoprodWith_cocone A x y).val binaryPointLeft =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKCoprodInl A
            ((cAlgVertexEquiv A).symm x) ((cAlgVertexEquiv A).symm y)))).edge := by
  simp only [barrattEcclesCoprodWith_cocone, coherentCoconeLegMap_ofDiagramEq]
  exact cAlgNativeCoprodCocone_leg_left A _ _

/-- 界面へ供給した余極限錐の第二脚も、同じ第二包含の区間全体。 -/
lemma barrattEcclesCoprodWith_cocone_leg_right (x y : (CAlg_R A) _⦋0⦌) :
    coherentCoconeLegMap (barrattEcclesCoprodWith_cocone A x y).val binaryPointRight =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKCoprodInr A
            ((cAlgVertexEquiv A).symm x) ((cAlgVertexEquiv A).symm y)))).edge := by
  simp only [barrattEcclesCoprodWith_cocone, coherentCoconeLegMap_ofDiagramEq]
  exact cAlgNativeCoprodCocone_leg_right A _ _

/-- BE の零 arity の増大は同型である。 -/
lemma barrattEcclesHopfZeroArity_isIso :
    IsIso ((hopf A).counit.map.app (FiniteBijection.of 0)) := by
  change IsIso ((augmentation A).map.app (FiniteBijection.of 0))
  rw [augmentation_app]
  exact zeroArity_augmentation_isIso A

/-- 既存の厳密な自然変換は第一包含を Hopf テンソルの標準射へ送る。 -/
lemma barrattEcclesCoproductTensorNat_inl (B D : (operad A).Algebra) :
    (coprod.inl : B ⟶ B ⨿ D) ≫ (barrattEcclesCoproductTensorNat A D).app B =
      hopfTensorInl (hopf A) (barrattEcclesHopfZeroArity_isIso A) B D :=
  coprod.inl_desc _ _

/-- 既存の厳密な自然変換は第二包含を Hopf テンソルの標準射へ送る。 -/
lemma barrattEcclesCoproductTensorNat_inr (B D : (operad A).Algebra) :
    (coprod.inr : D ⟶ B ⨿ D) ≫ (barrattEcclesCoproductTensorNat A D).app B =
      hopfTensorInr (hopf A) (barrattEcclesHopfZeroArity_isIso A) B D :=
  coprod.inr_desc _ _

/-- 第一包含の台は、複体の右単位子と第二因子の単位からの標準射。 -/
lemma barrattEcclesCoproductTensorNat_inl_carrier (B D : (operad A).Algebra) :
    ((coprod.inl : B ⟶ B ⨿ D) ≫ (barrattEcclesCoproductTensorNat A D).app B).hom =
      (ρ_ B.carrier).inv ≫ (𝟙 B.carrier ⊗ₘ
        (hopfTensorUnitMap (hopf A) (barrattEcclesHopfZeroArity_isIso A) D).hom) := by
  rw [barrattEcclesCoproductTensorNat_inl]
  rfl

/-- 第二包含の台は、複体の左単位子と第一因子の単位からの標準射。 -/
lemma barrattEcclesCoproductTensorNat_inr_carrier (B D : (operad A).Algebra) :
    ((coprod.inr : D ⟶ B ⨿ D) ≫ (barrattEcclesCoproductTensorNat A D).app B).hom =
      (λ_ D.carrier).inv ≫
        ((hopfTensorUnitMap (hopf A) (barrattEcclesHopfZeroArity_isIso A) B).hom ⊗ₘ
          𝟙 D.carrier) := by
  rw [barrattEcclesCoproductTensorNat_inr]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
