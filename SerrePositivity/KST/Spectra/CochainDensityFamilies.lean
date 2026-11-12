module

public import SerrePositivity.KST.Spectra.SimplexDensityDiagram
public import SerrePositivity.KST.Spectra.UnderlyingWeightedCochains
public import SerrePositivity.KST.Spectra.GroupUniversalCoverDiagram
public import SerrePositivity.KST.Spectra.SimplexTensorBoundary

/-!
概要：余単体 cochain への標準単体上の射と、重み・係数図式上の密度の族の比較。
方針：各 cochain 次数で end を uncurry し、二つの添字の自然性を交換する。
規約：係数も重みも任意の単体集合の図式。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。通常の Tot と完全な重みの end の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {W H : I ⥤ SSet.{u}} {A : SSet.{u}}

/-- 概要：cochain への標準単体上の射を図式上の密度の族として展開する。
方針：end の各成分の uncurry で二つの添字を交換する。
規約：全ての自然性を保持する実際の族。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot の Hom の密度による表示。 -/
def fromCochains (s : SimplexTensorBoundary.diagram A ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H) : DiagramFamily W H A where
  app i :=
    { app n := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.app n)).app i
      condition {n m} f k x α a := by
        have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.naturality f)
        change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry ((SSet.stdSimplex.map f ▷ A) ≫ s.app m) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.app n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre
            ((discreteLevels W).map f.op) H) at h
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre] at h
        have hi := NatTrans.congr_app h i
        have hk := NatTrans.congr_app hi k
        have h' := congr($(hk) (x, (α, a)))
        exact h'.symm }
  naturality {i j} f := by
    apply Family.ext
    intro n
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.app n)).naturality f

/-- 概要：図式上の密度の族の一つの次数を end のパラメーター付き族にする。
方針：図式上の自然性を各次数で評価する。
規約：パラメーターは標準単体と元のパラメーターとの直積。
使われ方：Goerss–Jardine VIII §1。密度比較の逆の各次数。 -/
def cochainFamily (s : DiagramFamily W H A) (n : SimplexCategory) :
    (discreteLevels W).obj (op n) ⊗
      (Functor.const I).obj (SSet.stdSimplex.obj n ⊗ A) ⟶ H where
  app i := (s.app i).app n
  naturality i j f := by
    have h := congrArg (fun t ↦ t.app n) (s.naturality f)
    exact h

/-- 概要：図式上の密度の族を cochain への標準単体上の自然変換に戻す。
方針：各次数で end へ持ち上げ、族の整合条件で余単体の自然性を示す。
規約：通常の自然変換であり Kan 条件を使わない。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot の密度表示の逆射。 -/
def toCochains (s : DiagramFamily W H A) : SimplexTensorBoundary.diagram A ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (cochainFamily s n)
  naturality n m f := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv _ H (SSet.stdSimplex.obj n ⊗ A)).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry ((SSet.stdSimplex.map f ▷ A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (cochainFamily s m)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (cochainFamily s n) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((discreteLevels W).map f.op) H)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    apply NatTrans.ext
    funext i
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    exact ((s.app i).condition f k x.1 x.2.1 x.2.2).symm

end

end SerrePositivity.KST.Spectra.SimplexDensity
