module

public import SerrePositivity.KST.Spectra.CochainDensityIso

/-!
概要：通常の Tot と完全な重みの end の密度比較は厳密な錐の標準射を保存する。
方針：各 cochain 次数で定数族を作り、恒等単体での対角評価を計算する。
規約：錐の極限性も Kan 条件も仮定しない。
使われ方：Goerss–Jardine VIII §§1–2。自明作用の標準射と基点保存の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet Opposite


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}

/-- 概要：厳密な錐を離散的単体の cochain の標準単体上の定数族へ送る。
方針：標準単体の変数を忘れて各次数の end の標準比較を合成する。
規約：錐の頂点を共通のパラメーターとする。
使われ方：Goerss–Jardine VIII §§1–2。Tot への厳密な錐の標準射。 -/
def coneFamily (c : Cone H) : SimplexTensorBoundary.diagram c.pt ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H where
  app n := snd (SSet.stdSimplex.obj n) c.pt ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison ((discreteLevels W).obj (op n)) c
  naturality n m f := by
    change (SSet.stdSimplex.map f ▷ c.pt) ≫ (snd _ _ ≫ _) =
      (snd _ _ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((discreteLevels W).map f.op) H
    rw [← Category.assoc, whiskerRight_snd, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_pre]

lemma diagramDiagonal_fromCone (c : Cone H) :
    diagramDiagonal (fromCochains (coneFamily W c)) =
      snd W ((Functor.const I).obj c.pt) ≫ c.π := by
  apply NatTrans.ext
  funext i
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry
      (snd (SSet.stdSimplex.obj k.unop) c.pt ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison ((discreteLevels W).obj k) c)).app i).app k
      (x.1, (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 k.unop), x.2)) =
    (c.π.app i).app k x.2
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
  rfl

/-- 概要：密度による Hom の同値は錐の定数族を完全な重みの標準射へ送る。
方針：Tot の lift と uncurry の両逆の後、対角評価の具体式を使う。
規約：実際の比較射の厳密な等式。
使われ方：Goerss–Jardine VIII §§1–2。自明作用と基点の標準射。 -/
lemma totalizationEndHomEquiv_cone (c : Cone H) :
    totalizationEndHomEquiv W H c.pt (CosimplicialTotalization.lift (coneFamily W c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (diagramDiagonal (fromCochains
    (CosimplicialTotalization.uncurry (CosimplicialTotalization.lift (coneFamily W c))))) = _
  have h := (totalizationHomEquiv _ c.pt).right_inv (coneFamily W c)
  change CosimplicialTotalization.uncurry (CosimplicialTotalization.lift (coneFamily W c)) =
    coneFamily W c at h
  rw [h, diagramDiagonal_fromCone]
  rfl

lemma totalizationEndIso_cone (c : Cone H) :
    CosimplicialTotalization.lift (coneFamily W c) ≫ (totalizationEndIso W H).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c := by
  rw [← totalizationEndHomEquiv_apply, totalizationEndHomEquiv_cone]

end

end SerrePositivity.KST.Spectra.SimplexDensity
