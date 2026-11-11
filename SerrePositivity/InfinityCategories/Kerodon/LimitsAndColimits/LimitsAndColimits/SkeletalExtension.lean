module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：単射の相対骨格に沿う写像の延長。
方針：各次数の境界充填を coproduct と pushout で貼り合わせる。
規約：モデル構造を使わず、Mathlib の相対セル分解だけを使う。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の極限側のセルごとの延長。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対骨格の各セルの境界が充填できれば次の骨格へ延長できる。
方針：選んだ充填を coproduct にまとめ、骨格の pushout から射を取る。
規約：単射の相対セル分解の一段を扱う。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の次元による延長。 -/
lemma exists_extension_skeletonOfMono_succ {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (d : ℕ) (f : (skeletonOfMono i d : SSet.{u}) ⟶ X)
    (hf : ∀ c : Cell i d, ∃ F : (Δ[d] : SSet.{u}) ⟶ X,
      (boundary d).ι ≫ F = c.ιSigmaBoundary ≫ t i d ≫ f) :
    ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X, r i d ≫ F = f := by
  classical
  let g : sigmaStdSimplex i d ⟶ X := Sigma.desc (fun c ↦ (hf c).choose)
  have hg : l i d ≫ g = t i d ≫ f := by
    apply Sigma.hom_ext
    intro c
    rw [← Category.assoc, Cell.ι_l, Category.assoc]
    change (boundary d).ι ≫ (Sigma.ι (fun _ : Cell i d ↦ (Δ[d] : SSet.{u})) c ≫ g) = _
    rw [Sigma.ι_comp_desc]
    exact (hf c).choose_spec
  exact ⟨(isPushout i d).desc f g hg.symm, (isPushout i d).inl_desc _ _ _⟩

/-- 概要：単射の始域は各相対骨格へ自然に含まれる。
方針：元の単射の像が相対骨格に含まれることを使う。
規約：単射性自体はこの射の定義に不要。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の指定済み部分の固定。 -/
def skeletonBase {A B : SSet.{u}} (i : A ⟶ B) (d : ℕ) :
    A ⟶ (skeletonOfMono i d : SSet.{u}) := Subcomplex.lift i le_sup_left

/-- 概要：相対骨格への始域の包含は次元を上げても一致する。
方針：部分型の外側への包含で比較する。
規約：相対骨格の一段の射 r を使う。
使われ方：Kerodon §7.1.8（Tag 02X8） の延長の帰納法の固定条件。 -/
lemma skeletonBase_succ {A B : SSet.{u}} (i : A ⟶ B) (d : ℕ) :
    skeletonBase i d ≫ r i d = skeletonBase i (d + 1) := rfl

/-- 概要：零番目の相対骨格は単射の始域と同型。
方針：零骨格が空であることと、単射から像への同型を使う。
規約：同型の逆射は skeletonBase i 0。
使われ方：Kerodon §7.1.8（Tag 02X8） のセル延長の初期条件。 -/
noncomputable def skeletonBaseZeroIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (skeletonOfMono i 0 : SSet.{u}) ≅ A :=
  Subcomplex.eqToIso (skeletonOfMono_zero i) ≪≫ (asIso (Subcomplex.toRange i)).symm

/-- 概要：零番目の相対骨格の同型の逆は始域の包含。
方針：像への包含で比較する。
規約：単射を仮定する。
使われ方：Kerodon §7.1.8（Tag 02X8） の帰納法の開始。 -/
lemma skeletonBaseZeroIso_inv {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (skeletonBaseZeroIso i).inv = skeletonBase i 0 := by
  apply (cancel_mono (skeletonOfMono i 0).ι).1
  simp [skeletonBaseZeroIso, skeletonBase]

/-- 概要：全ての相対骨格で指定部分を固定して一段延長できれば全体へ延長できる。
方針：自然数上で互換な延長を選び、相対骨格の余極限から射を取る。
規約：開始する射 a を全ての段階で厳密に固定する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） のセル延長の組み立て。 -/
lemma exists_extension_of_skeletal_extensions {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (a : A ⟶ X)
    (hstep : ∀ d (f : (skeletonOfMono i d : SSet.{u}) ⟶ X),
      skeletonBase i d ≫ f = a →
        ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X, r i d ≫ F = f) :
    ∃ F : B ⟶ X, i ≫ F = a := by
  classical
  let P (d : ℕ) := { f : (skeletonOfMono i d : SSet.{u}) ⟶ X // skeletonBase i d ≫ f = a }
  have hinit : skeletonBase i 0 ≫ ((skeletonBaseZeroIso i).hom ≫ a) = a := by
    rw [← skeletonBaseZeroIso_inv, Iso.inv_hom_id_assoc]
  let init : P 0 := ⟨(skeletonBaseZeroIso i).hom ≫ a, hinit⟩
  have step (d : ℕ) (f : P d) : ∃ F : P (d + 1), r i d ≫ F.val = f.val := by
    obtain ⟨F, hF⟩ := hstep d f.val f.property
    refine ⟨⟨F, ?_⟩, hF⟩
    rw [← skeletonBase_succ i d, Category.assoc, hF]
    exact f.property
  let fs : (d : ℕ) → P d := fun d ↦ Nat.rec init (fun n f ↦ (step n f).choose) d
  have hfs (d : ℕ) : r i d ≫ (fs (d + 1)).val = (fs d).val :=
    (step d (fs d)).choose_spec
  let c := SSet.relativeCellComplexOfMono i
  have hn (n m : ℕ) (hnm : n ≤ m) :
      c.F.map (homOfLE hnm) ≫ (fs m).val = (fs n).val := by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have he : (homOfLE (Nat.le_succ_of_le hm) : n ⟶ m + 1) =
          homOfLE hm ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
      rw [he, CategoryTheory.Functor.map_comp, Category.assoc]
      change c.F.map (homOfLE hm) ≫ (r i m ≫ (fs (m + 1)).val) = _
      rw [hfs, ih]
  let C : Cocone c.F :=
    { pt := X
      ι :=
        { app := fun n ↦ (fs n).val
          naturality := fun n m α ↦ by
            change c.F.map α ≫ (fs m).val = (fs n).val ≫ 𝟙 X
            have hα : homOfLE (leOfHom α) = α := Subsingleton.elim _ _
            simpa only [Category.comp_id, hα] using hn n m (leOfHom α) } }
  refine ⟨c.isColimit.desc C, ?_⟩
  have hi : skeletonBase i 0 ≫ c.incl.app 0 = i := Subcomplex.lift_ι _ _
  calc
    i ≫ c.isColimit.desc C = (skeletonBase i 0 ≫ c.incl.app 0) ≫ c.isColimit.desc C :=
      congrArg (fun j ↦ j ≫ c.isColimit.desc C) hi.symm
    _ = skeletonBase i 0 ≫ (fs 0).val := by rw [Category.assoc, c.isColimit.fac C 0]
    _ = a := (fs 0).property

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
