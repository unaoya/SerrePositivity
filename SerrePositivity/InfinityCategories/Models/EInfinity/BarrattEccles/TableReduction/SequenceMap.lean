module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CochainMap
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NormalizedAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Sequence
public import SerrePositivity.EInfinity.BarrattEccles.Sequence

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：TR 鎖写像は BE の右作用を χ の逆左作用へ送る（BF §1.3.6）。
方針：各次数の正規化 TR の同変性を複体射の外延性でまとめる。
規約：右置換 ρ は値の置換 ρ⁻¹ に対応する。
使われ方：整数複体の作用との可換性へ延長する。 -/
lemma chainMap_rightAction (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChainMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.rightAction n ρ) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap A n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap A n ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedRename A n ρ⁻¹ := by
  ext d : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_rightAction A n d ρ x

/-- 概要：整数 TR も BE の右作用を χ の逆左作用へ送る（BF §1.3.6）。
方針：鎖射の可換性を次数延長関手で送る。
規約：全整数次数の複体射としての等式。
使われ方：対称列上の TR の自然性。 -/
lemma cochainMap_rightAction (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.complexRightAction A n ρ ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n ρ⁻¹ := by
  have h := congrArg ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap_rightAction A n ρ)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact h

/-- 概要：整数コチェインの全射 TR の対称列の射（BF §1.3）。
方針：各 arity の cochainMap と逆右作用・左作用の可換性を自然変換にまとめる。
規約：arity 零と任意の可換環を含む。
使われ方：TR の対称 dg オペラッド射の台の自然変換。 -/
def sequenceMap : _root_.SerrePositivity.EInfinity.BarrattEccles.sequence A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence A where
  app X := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (_root_.SerrePositivity.FiniteBijection.card X)
  naturality {X Y} f := by
    obtain rfl := _root_.SerrePositivity.FiniteBijection.object_eq_of_hom f
    change (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicialSequenceMap f) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (_root_.SerrePositivity.FiniteBijection.card X) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A (_root_.SerrePositivity.FiniteBijection.card X) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequenceMap A f
    rw [_root_.SerrePositivity.EInfinity.BarrattEccles.simplicialSequenceMap_self, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequenceMap_self]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_rightAction A (_root_.SerrePositivity.FiniteBijection.card X) (_root_.SerrePositivity.FiniteBijection.equivOfHom f).symm

/-- 概要：対称列 TR の第 n 成分は構成した整数 TR（BF §1.3）。
方針：自然変換を標準 n 元対象で評価する。
規約：定義による等式。
使われ方：合成と単位の保存を arity ごとの複体射へ戻す。 -/
lemma sequenceMap_app (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sequenceMap A).app (_root_.SerrePositivity.FiniteBijection.of n) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
