module

public import SerrePositivity.Spectra.SymmetricSequence.DayAdjunction
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-!
# 基点付き単体的集合の対称列

構成した smash の閉対称モノイダル基盤と、対称列の convolution を接続する。
各段の積は外部 smash、convolution は直和に沿う左 Kan 拡張。
convolution の閉対称モノイダル構造を登録済み。
内部 Hom は end による構成であり、評価・余評価と随伴を備える。球面対称列の加群は別に扱う。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SerrePositivity

/-- 基点付き単体的集合に値を取る対称列。 -/
abbrev PointedSymmetricSequence := SymmetricSequence PointedSimplicialSet.{u}

namespace PointedSymmetricSequence

open CategoryTheory

example : MonoidalCategory PointedSymmetricSequence.{u} := inferInstance
example : SymmetricCategory PointedSymmetricSequence.{u} := inferInstance
example : MonoidalClosed PointedSymmetricSequence.{u} := inferInstance

/-- 二つの対称列の通常の smash convolution。 -/
noncomputable abbrev convolution (F G : PointedSymmetricSequence.{u}) :
    PointedSymmetricSequence.{u} := SymmetricSequence.convolution F G

/-- 和次数への構造射。後で球面対称列の乗法や加群作用に使う。 -/
noncomputable def convolutionPairing (F G : PointedSymmetricSequence.{u}) (p q : ℕ) :
    PointedObject.smash (SymmetricSequence.level F p) (SymmetricSequence.level G q) ⟶
      SymmetricSequence.level (convolution F G) (p + q) :=
  (SymmetricSequence.convolutionUnit F G).app (FiniteBijection.of p, FiniteBijection.of q)

/-- 和次数への構造射は、二つのブロックの置換作用と両立する。 -/
lemma convolutionPairing_equivariance (F G : PointedSymmetricSequence.{u}) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    PointedObject.smashMap (F.map (FiniteBijection.permutation p σ))
        (G.map (FiniteBijection.permutation q τ)) ≫ convolutionPairing F G p q =
      convolutionPairing F G p q ≫ (convolution F G).map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  have h := (SymmetricSequence.convolutionUnit F G).naturality
    (show (FiniteBijection.of p, FiniteBijection.of q) ⟶
        (FiniteBijection.of p, FiniteBijection.of q) from
      (FiniteBijection.permutation p σ, FiniteBijection.permutation q τ))
  change (PointedObject.smashMap (F.map (FiniteBijection.permutation p σ)) (𝟙 _) ≫
      PointedObject.smashMap (𝟙 _) (G.map (FiniteBijection.permutation q τ))) ≫
      convolutionPairing F G p q = convolutionPairing F G p q ≫
        (convolution F G).map (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) at h
  simpa only [PointedObject.smashMap_comp, Category.id_comp, Category.comp_id] using h

/-- end による基点付き対称列の内部 Hom の関手。 -/
abbrev internalHomFunctor (F : PointedSymmetricSequence.{u}) :
    PointedSymmetricSequence.{u} ⥤ PointedSymmetricSequence.{u} :=
  SymmetricSequence.internalHomFunctor F

end PointedSymmetricSequence
end SerrePositivity
