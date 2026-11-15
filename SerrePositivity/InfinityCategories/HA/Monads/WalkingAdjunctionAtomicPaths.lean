module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicWords

/-!
概要：全次数の原子的な射のquiverと、自由な道から実射への全射的な比較を構成する。
方針：原子的な語を有限の道へ展開し、実合成による像を照合する。
規約：完全性だけを証明し、忠実性や退化との両立を仮定しない。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：原子的な射のquiverの対象。
方針：同じ次数の二対象を包む。規約：既存の全射の圏とはquiverの構造を分離する。
使われ方：Riehl–Verity Definition 2.1.4 の原子的な生成quiver。 -/
structure WalkingAdjunctionAtomicVertex (n : ℕ) where
  level : WalkingAdjunctionLevel n

/-- 概要：実際の原子的なn射を生成射とするquiver。
方針：元の実射と原子性の証明の部分型を取る。
規約：生成射の存在を仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
instance walkingAdjunctionAtomicQuiver (n : ℕ) : Quiver (WalkingAdjunctionAtomicVertex n) where
  Hom X Y := {F : X.level ⟶ Y.level // WalkingAdjunctionLevelIsAtomic F}

/-- 概要：原子的な射のquiverから元の全n射の圏への包含。
方針：部分型の元の射を取る。規約：同じ二対象。
使われ方：Riehl–Verity Proposition 3.1.10 の自由な圏との比較。 -/
def walkingAdjunctionAtomicPrefunctor (n : ℕ) :
    WalkingAdjunctionAtomicVertex n ⥤q WalkingAdjunctionLevel n where
  obj X := X.level
  map f := f.val

/-- 概要：原子的な射の道を実際に水平合成する比較関手。
方針：自由な道の普遍性を使う。規約：全次数の全ての有限の道。
使われ方：Riehl–Verity Proposition 3.1.10 の自由な圏への比較。 -/
def walkingAdjunctionAtomicPathFunctor (n : ℕ) :
    Paths (WalkingAdjunctionAtomicVertex n) ⥤ WalkingAdjunctionLevel n :=
  Paths.lift (walkingAdjunctionAtomicPrefunctor n)

/-- 概要：原子的な語のデータから、同じ始点・終点の道を作る。
方針：空の語・原子的な語・合成を、それぞれ空の道・一段の道・道の合成へ送る。
規約：存在だけでなく実際の道を与える。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionAtomicWord.toPath {n : ℕ} {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y}
    (a : WalkingAdjunctionAtomicWord n F) :
    Quiver.Path (V := WalkingAdjunctionAtomicVertex n) ⟨X⟩ ⟨Y⟩ := by
  induction a with
  | nil X => exact .nil
  | atom F h => exact (show (⟨_⟩ : WalkingAdjunctionAtomicVertex n) ⟶ ⟨_⟩ from ⟨F, h⟩).toPath
  | comp a b pa pb => exact pa.comp pb

/-- 概要：語から作った道の実像は元のn射そのもの。
方針：語に関する帰納法と比較関手の合成保存を使う。
規約：全射の等式。使われ方：Riehl–Verity Proposition 3.1.10 の全射性の検収。 -/
lemma WalkingAdjunctionAtomicWord.toPath_map {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) :
    (walkingAdjunctionAtomicPathFunctor n).map a.toPath = F := by
  induction a with
  | nil X => rfl
  | atom F h => exact Paths.lift_toPath (walkingAdjunctionAtomicPrefunctor n) ⟨F, h⟩
  | comp a b ha hb =>
    change (walkingAdjunctionAtomicPathFunctor n).map (a.toPath ≫ b.toPath) = _
    rw [CategoryTheory.Functor.map_comp, ha, hb]

/-- 概要：全次数の全ての実n射は原子的な道の像である。
方針：長さの帰納法で得た有限の語を実際の道へ展開する。
規約：忠実性は別に証明する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
instance walkingAdjunctionAtomicPathFunctor_full (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Full where
  map_surjective {X Y} F := by
    obtain ⟨a⟩ := walkingAdjunctionAtomicWord_nonempty F
    exact ⟨a.toPath, a.toPath_map⟩

end SerrePositivity.InfinityCategories.HA.Monads
