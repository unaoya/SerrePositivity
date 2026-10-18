module

public import SerrePositivity.KST.Comparison.FreeColumns
public import SerrePositivity.KST.Comparison.FatNormalFormAction

/-!
# fat realization と列の自由な退化の対角との同型

概要：次数ごとの全射な標準形の同値が単体作用と両立することを証明する。
方針：両方の作用を像分解による正規化で計算する。
規約：Segal 1974 Proposition 1.6 の fat realization と通常の対角の比較の補助。
使われ方：各列の augmentation の対角の局所化可逆性を fat realization へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open SerrePositivity.BisimplicialModel

/--
概要：fat realization と列の自由な退化の次数ごとの同型は単体作用と可換。
方針：標準形の正規化の作用と、列の写像の作用を両辺で比較する。
規約：内側と外側の二作用の交換は元の自然性から得る。
使われ方：実際の単体集合の同型の自然性。
-/
theorem fatFreeColumnsDegreeIso_naturality (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e) :
    (fatRealization F).map θ ≫ (fatFreeColumnsDegreeIso F e).hom =
      (fatFreeColumnsDegreeIso F d).hom ≫ (diagonal.obj (freeColumns F)).map θ := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (freeDegeneraciesNormalForm (F.flip.obj e) e).injective
  change fatDegreeNormalize (discreteRowsFunctor.obj (F.flip.obj e)) e
    (fatNormalFormRealize _ _ (fatColumnNormalFormEquiv F e
      (fatDegreeNormalize F e ((fatRealization F).map θ x)))) =
    fatDegreeNormalize (discreteRowsFunctor.obj (F.flip.obj e)) e
      ((fatRealization (discreteRowsFunctor.obj (F.flip.obj e))).map θ
        ((fatRealizationMap (discreteRowsFunctor.map (F.flip.map θ))).app d
          (fatNormalFormRealize _ _ (fatColumnNormalFormEquiv F d (fatDegreeNormalize F d x)))))
  rw [fatDegreeNormalize_realize, fatNormalFormRealize_map,
    fatDegreeNormalize_action, fatDegreeNormalize_action, fatDegreeNormalize_realize]
  rfl

/--
概要：fat realization は各列の自由な退化の対角と実際に同型である。
方針：各次数の標準形の同型と単体作用との整合をまとめる。
規約：局所化前の単体集合の同型。
使われ方：対角への自然な比較の局所化可逆性。
-/
def fatFreeColumnsIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    fatRealization F ≅ diagonal.obj (freeColumns F) :=
  NatIso.ofComponents (fatFreeColumnsDegreeIso F) (fatFreeColumnsDegreeIso_naturality F)

end SerrePositivity.KST.Comparison
