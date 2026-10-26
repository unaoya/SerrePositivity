module
public import SerrePositivity.KST.SConstruction.Cofinality.CutCokernelEquiv

/-!
概要：指定射の S 余核の制限写像の厳密な関手則と零段。
方針：元の K₀ の代表上で端点制限の合成・恒等・定値の式を検査する。
規約：全ての等号は元の指定射の余核上の等号。
使われ方：元の S 余核の単体図式と bar 座標の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：余核の制限は端点写像の合成を反変に保つ。
方針：商の代表上で元の K₀ の合成則を使う。
規約：全端点写像を許す。
使われ方：元の余核図式の関手則。 -/
lemma cutCokernelRestriction_comp {l m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (θ : Fin (l + 1) →o Fin (m + 1)) (φ : Fin (m + 1) →o Fin (n + 1)) :
    cutCokernelRestriction f (φ.comp θ) =
      (cutCokernelRestriction f θ).comp (cutCokernelRestriction f φ) := by
  apply AddMonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h a => ?_
  exact congrArg (QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap ((sEndofunctor l).map f)).range)
    (DFunLike.congr_fun (cutKZeroRestriction_comp Y θ φ) a)

/-- 概要：余核の恒等制限は恒等準同型。
方針：元の K₀ の恒等則を商へ写す。
規約：同じ S_n 射の余核を使う。
使われ方：一辺の座標比較。 -/
lemma cutCokernelRestriction_id (n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    cutCokernelRestriction f (OrderHom.id : Fin (n + 1) →o _) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h a => ?_
  exact congrArg (QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range)
    (DFunLike.congr_fun (cutKZeroRestriction_id n Y) a)

/-- 概要：定値端点制限の余核上の作用は零。
方針：元の K₀ の定値消滅を商へ写す。
規約：零対象を選び直さない。
使われ方：bar の退化単体の零座標。 -/
lemma cutCokernelRestriction_constant {m n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (i : Fin (n + 1)) :
    cutCokernelRestriction f (OrderHom.const (Fin (m + 1)) i) = 0 := by
  apply AddMonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h a => ?_
  have h := congrArg (QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap ((sEndofunctor m).map f)).range)
    (DFunLike.congr_fun (cutKZeroRestriction_constant (m := m) Y i) a)
  exact h.trans (map_zero _)

/-- 概要：元の零段 S_0 射の K₀ 余核は一元集合。
方針：Fin 1 の恒等は定値であり、その作用は恒等かつ零となる。
規約：元の未置換零段の K₀ 余核。
使われ方：bar 座標の零段の同型。 -/
lemma cutKZeroCokernel_zero_subsingleton {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Subsingleton (cutKZeroCokernel 0 f) := by
  have he : (OrderHom.id : Fin (0 + 1) →o _) = OrderHom.const (Fin 1) (0 : Fin 1) :=
    by
      apply DFunLike.ext
      intro i
      apply Fin.ext
      have := i.isLt
      change i.val = 0
      omega
  have h := (cutCokernelRestriction_id 0 f).symm.trans
    ((congrArg (cutCokernelRestriction f) he).trans (cutCokernelRestriction_constant f _))
  constructor
  intro a b
  exact (DFunLike.congr_fun h a).trans (DFunLike.congr_fun h b).symm

end SerrePositivity.KST.SConstruction.Cofinality
