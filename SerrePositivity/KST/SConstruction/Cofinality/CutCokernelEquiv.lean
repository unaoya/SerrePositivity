module
public import SerrePositivity.KST.SConstruction.Cofinality.CutCokernelRestriction

/-!
概要：元の S_n 射の K₀ 余核を左右の区間の余核へ分解する。
方針：K₀ 区間同型の自然性で分母の像を直積の像へ写す。
規約：完備化も共終性も仮定せず、元の指定射の余核を保つ。
使われ方：障害群の全単体的 bar 同定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：元の K₀ 区間同型は元の完全射と可換。
方針：二つの元の制限の自然性を合わせる。
規約：同型の順射は元の左右の制限。
使われ方：余核の分母の直積同定。 -/
lemma cutKZeroEquiv_naturality (n : ℕ) (k : Fin (n + 1))
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier)) :
    cutKZeroEquiv n k Y (triangulatedKZeroSourceMap ((sEndofunctor n).map f) a) =
      (triangulatedKZeroSourceMap ((sEndofunctor k.val).map f) (cutKZeroEquiv n k X a).1,
       triangulatedKZeroSourceMap ((sEndofunctor (n - k.val)).map f)
         (cutKZeroEquiv n k X a).2) :=
  Prod.ext (DFunLike.congr_fun (cutKZeroRestriction_naturality f _) a)
    (DFunLike.congr_fun (cutKZeroRestriction_naturality f _) a)

/-- 概要：元の S_n 射の K₀ 像は区間同型で左右の K₀ 像の直積へ写る。
方針：自然性で順包含を示し、始域の区間同型の逆で同時持ち上げを作る。
規約：左右の持ち上げを別の S_n 対象として扱わない。
使われ方：指定射の余核への区間同型の降下。 -/
lemma cutKZeroEquiv_range (n : ℕ) (k : Fin (n + 1))
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range.map
        (cutKZeroEquiv n k Y).toAddMonoidHom =
      (triangulatedKZeroSourceMap ((sEndofunctor k.val).map f)).range.prod
        (triangulatedKZeroSourceMap ((sEndofunctor (n - k.val)).map f)).range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨⟨(cutKZeroEquiv n k X a).1,
      (congrArg Prod.fst (cutKZeroEquiv_naturality n k f a)).symm⟩,
      ⟨(cutKZeroEquiv n k X a).2,
        (congrArg Prod.snd (cutKZeroEquiv_naturality n k f a)).symm⟩⟩
  · rintro ⟨_, _⟩ ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    let c := (cutKZeroEquiv n k X).symm (a, b)
    refine ⟨triangulatedKZeroSourceMap ((sEndofunctor n).map f) c, ⟨c, rfl⟩, ?_⟩
    exact (cutKZeroEquiv_naturality n k f c).trans
      (congrArg (fun p =>
        (triangulatedKZeroSourceMap ((sEndofunctor k.val).map f) p.1,
         triangulatedKZeroSourceMap ((sEndofunctor (n - k.val)).map f) p.2))
        ((cutKZeroEquiv n k X).apply_symm_apply (a, b)))

/-- 概要：指定射の元の S_n K₀ 余核の区間直積同型。
方針：K₀ 区間同型を元の像で割り、直積の商の標準同型を合成する。
規約：左右の余核は同じ元の指定射から作る。
使われ方：離散的障害の S 方向 Segal 分解。 -/
def cutCokernelEquiv (n : ℕ) (k : Fin (n + 1))
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    cutKZeroCokernel n f ≃+ cutKZeroCokernel k.val f × cutKZeroCokernel (n - k.val) f :=
  (QuotientAddGroup.congr
    (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range
    ((triangulatedKZeroSourceMap ((sEndofunctor k.val).map f)).range.prod
      (triangulatedKZeroSourceMap ((sEndofunctor (n - k.val)).map f)).range)
    (cutKZeroEquiv n k Y) (cutKZeroEquiv_range n k f)).trans
      (QuotientAddGroup.prodAddEquiv _ _)

/-- 概要：余核区間同型の順射は元の二つの制限を厳密に回収する。
方針：商の代表上で同型の二つの標準計算公式を使う。
規約：同型の順射を抽象的な全単射で取り替えない。
使われ方：元の全単体的障害図式の Segal 写像との照合。 -/
lemma cutCokernelEquiv_apply (n : ℕ) (k : Fin (n + 1))
    {X Y : StableModel.{u}} (f : X ⟶ Y) (a : cutKZeroCokernel n f) :
    cutCokernelEquiv n k f a =
      (cutCokernelRestriction f (cutLeftIntervalInclusion n k) a,
       cutCokernelRestriction f (cutRightIntervalInclusion n k) a) := by
  induction a using Quotient.inductionOn with | h a => ?_
  rfl

end SerrePositivity.KST.SConstruction.Cofinality
