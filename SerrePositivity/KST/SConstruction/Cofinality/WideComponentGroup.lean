module
public import SerrePositivity.KST.SConstruction.Cofinality.WideComponentAddition
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionStabilization
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
概要：元の指定完備化射の wide 成分を可換群として束ねる。
方針：本質像の零成分判定と D-22 の双積懸垂の像回収から加法逆元を作る。
規約：群構造を明示的なデータとして返し、推論不能な完備化証拠を instance にしない。
使われ方：離散的障害と元の K₀ 余核の群同定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の本質像に入る対象の wide 成分は零成分である。
方針：像成分の基点判定を対象と選択零頂点に適用する。
規約：元の本質像を拡大せずに零成分を判定する。
使われ方：双積懸垂の像回収を加法逆元の存在へ移す。 -/
lemma completionWideObjectClass_zero_of_image (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (ha : a.as.as ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) :
    completionWideObjectClass r ι f hf a = completionWideZero r ι f hf := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let hF := multiSEndofunctor_map_isIdempotentCompletion r ι f hf
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj Y).carrier
  let x := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj X).carrier).vertex
  let va : (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) _⦋0⦌ :=
    ⟨a.as.as, LocalizingInvariants.completionCofiberWide_vertex F.val hF a.as.as⟩
  let vz : (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) _⦋0⦌ :=
    ⟨z.vertex, LocalizingInvariants.completionCofiberWide_vertex F.val hF z.vertex⟩
  have hA := (completionWideImageComponent_iff_basepoint r ι f hf x va).mp ha
  have hZ := (completionWideImageComponent_iff_basepoint r ι f hf x vz).mp
    ((completionImageClosedPredicate r ι f hf).zero_mem z.isZero)
  exact hA.trans hZ.symm

/-- 概要：対象とその一回シフトの双積の wide 成分は零。
方針：D-22 の同じ全多次数への適用で元の本質像への所属を得る。
規約：元の対象自体が本質像に入るとは結論しない。
使われ方：成分の加法逆元の存在。 -/
lemma completionWideObjectClass_biprod_shift_zero (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionWideObjectClass r ι f hf (a ⊞
      (shiftFunctor (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
        (1 : ℤ)).obj a) = completionWideZero r ι f hf := by
  obtain ⟨c, ⟨e⟩⟩ := multiSBiprodShift_mem_image_of_completion r ι f hf a
  obtain ⟨c, rfl⟩ := Truncated.HomotopyCategory.mk_surjective c
  apply completionWideObjectClass_zero_of_image r ι f hf
  exact ⟨c, ⟨e.symm⟩⟩

/-- 概要：wide 成分の双積和の全ての元は加法逆元を持つ。
方針：元を実頂点で表し、その一回シフトの成分を逆元にする。
規約：代表頂点の選択は存在証明の中だけで使う。
使われ方：明示的な可換群データの構成。 -/
lemma completionWideAdd_exists_inverse (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    ∃ b, completionWideAdd r ι f hf b a = completionWideZero r ι f hf := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  let A : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier :=
    HomotopyCategory.mk a.val
  let B := (shiftFunctor (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (1 : ℤ)).obj A
  refine ⟨completionWideObjectClass r ι f hf B, ?_⟩
  exact (completionWideAdd_comm r ι f hf _ _).trans
    ((completionWideAdd_objectClass r ι f hf A B).trans
      (completionWideObjectClass_biprod_shift_zero r ι f hf A))

/-- 概要：元の wide 成分の双積演算は可換群を定める。
方針：結合則・零元・逆元の存在を最小公理から束ね、交換則を加える。
規約：完備化証拠を含む明示的な構造データとして返す。
使われ方：K₀ の普遍性へ渡す離散的障害の群構造。 -/
@[instance_reducible] def completionWideAddCommGroup (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    AddCommGroup (SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) := by
  let T := SSet.π₀ (LocalizingInvariants.completionCofiberWide
    (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})
  let : Add T := ⟨completionWideAdd r ι f hf⟩
  let : Zero T := ⟨completionWideZero r ι f hf⟩
  let : Neg T := ⟨fun a => Classical.choose (completionWideAdd_exists_inverse r ι f hf a)⟩
  let G : AddGroup T := AddGroup.ofLeftAxioms (completionWideAdd_assoc r ι f hf)
    (completionWideAdd_zero_left r ι f hf)
    (fun a => Classical.choose_spec (completionWideAdd_exists_inverse r ι f hf a))
  exact { G with add_comm := completionWideAdd_comm r ι f hf }

end SerrePositivity.KST.SConstruction.Cofinality
