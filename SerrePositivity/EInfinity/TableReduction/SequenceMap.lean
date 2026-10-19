module

public import SerrePositivity.EInfinity.TableReduction.CochainMap
public import SerrePositivity.EInfinity.TableReduction.NormalizedAction
public import SerrePositivity.EInfinity.Surjection.Sequence
public import SerrePositivity.EInfinity.BarrattEccles.Sequence

/-!
# TR の対称列の射

概要：Berger–Fresse §1.3 の一般の全射 TR を整数複体の対称列の射へまとめる。
方針：正規化作用の可換性を鎖射の等式にし、零延長で整数複体の自然性へ移す。
規約：共変な対称列には BE の逆右作用と χ の左ラベル置換を対応させる。
使われ方：TR オペラッド射の map 成分。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：TR 鎖写像は BE の右作用を χ の逆左作用へ送る（BF §1.3.6）。
方針：各次数の正規化 TR の同変性を複体射の外延性でまとめる。
規約：右置換 ρ は値の置換 ρ⁻¹ に対応する。
使われ方：整数複体の作用との可換性へ延長する。 -/
lemma chainMap_rightAction (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    BarrattEccles.normalizedChainMap A (BarrattEccles.rightAction n ρ) ≫ chainMap A n =
      chainMap A n ≫ Surjection.normalizedRename A n ρ⁻¹ := by
  ext d : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact normalizedMap_rightAction A n d ρ x

/-- 概要：整数 TR も BE の右作用を χ の逆左作用へ送る（BF §1.3.6）。
方針：鎖射の可換性を次数延長関手で送る。
規約：全整数次数の複体射としての等式。
使われ方：対称列上の TR の自然性。 -/
lemma cochainMap_rightAction (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    BarrattEccles.complexRightAction A n ρ ≫ cochainMap A n =
      cochainMap A n ≫ Surjection.complexRename A n ρ⁻¹ := by
  have h := congrArg ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map)
    (chainMap_rightAction A n ρ)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact h

/-- 概要：整数コチェインの全射 TR の対称列の射（BF §1.3）。
方針：各 arity の cochainMap と逆右作用・左作用の可換性を自然変換にまとめる。
規約：arity 零と任意の可換環を含む。
使われ方：TR の対称 dg オペラッド射の台の自然変換。 -/
def sequenceMap : BarrattEccles.sequence A ⟶ Surjection.sequence A where
  app X := cochainMap A (FiniteBijection.card X)
  naturality {X Y} f := by
    obtain rfl := FiniteBijection.object_eq_of_hom f
    change (BarrattEccles.normalizedFunctor A).map (BarrattEccles.simplicialSequenceMap f) ≫
      cochainMap A (FiniteBijection.card X) =
        cochainMap A (FiniteBijection.card X) ≫ Surjection.sequenceMap A f
    rw [BarrattEccles.simplicialSequenceMap_self, Surjection.sequenceMap_self]
    exact cochainMap_rightAction A (FiniteBijection.card X) (FiniteBijection.equivOfHom f).symm

/-- 概要：対称列 TR の第 n 成分は構成した整数 TR（BF §1.3）。
方針：自然変換を標準 n 元対象で評価する。
規約：定義による等式。
使われ方：合成と単位の保存を arity ごとの複体射へ戻す。 -/
lemma sequenceMap_app (n : ℕ) :
    (sequenceMap A).app (FiniteBijection.of n) = cochainMap A n := rfl

end SerrePositivity.EInfinity.TableReduction
