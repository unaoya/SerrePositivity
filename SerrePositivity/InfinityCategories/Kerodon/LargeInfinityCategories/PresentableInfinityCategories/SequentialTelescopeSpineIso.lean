module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialTelescopeSpineMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.SequentialSpineInnerAnodyne
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：望遠鏡の strict pushout は、元の可算 spine と厳密に同型。
方針：端点の正方形の pullback と、端点外の区間単体の単射性で pushout の単射性を示す。
規約：元の可算 nerve への写像を保持して比較する。
使われ方：P-11 の可算列の余積・pushout 計算。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：区間成分が定値の単体は、元の離散端点族から来る。
方針：区間番号も定値なので、最初の頂点の対で定値な離散単体を作る。
規約：全高次単体を厳密に回収する。
使われ方：端点の pullback と端点外での単射性。 -/
lemma sequentialTelescopeInterval_mem_boundary {d : ℕ}
    (b : (nerve (Discrete (ULift.{u} ℕ) × Fin 2)) _⦋d⦌)
    (hb : ∀ i, (b.obj i).2 = (b.obj 0).2) :
    b ∈ Set.range ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app (Opposite.op ⦋d⦌)) := by
  let a : (nerve (Discrete (ULift.{u} ℕ × Fin 2))) _⦋d⦌ :=
    (CategoryTheory.Functor.const (Fin (d + 1))).obj
      (Discrete.mk ((b.obj 0).1.as, (b.obj 0).2))
  refine ⟨a, ?_⟩
  change a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u} = b
  exact CategoryTheory.Functor.ext (fun i ↦
    Prod.ext (Discrete.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeInterval_index_eq b i).symm) (hb i).symm)
    (fun _ _ _ ↦ CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- 概要：離散端点の外にある区間単体の最初の端点番号は零。
方針：最初が一なら単調性により全区間成分が一となり、離散端点から来る。
規約：元の区間成分の番号を比較する。
使われ方：非定値な区間から可算番号を一意に回収する。 -/
lemma sequentialTelescopeInterval_nonboundary_start {d : ℕ}
    (b : (nerve (Discrete (ULift.{u} ℕ) × Fin 2)) _⦋d⦌)
    (hb : b ∉ Set.range
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app (Opposite.op ⦋d⦌))) :
    (b.obj 0).2.val = 0 := by
  by_contra hzero
  apply hb
  apply sequentialTelescopeInterval_mem_boundary b
  intro i
  have hi := leOfHom (b.map (homOfLE (Fin.zero_le i))).2
  have hi' := (b.obj i).2.isLt
  have h0' := (b.obj 0).2.isLt
  apply Fin.ext
  omega

/-- 概要：元の可算 nerve への区間写像は、離散端点の外で単射。
方針：最初の端点番号が零なので可算番号を回収し、各頂点の残りの番号を回収する。
規約：端点では二つの隣接区間が同じ頂点に貼られることを許す。
使われ方：望遠鏡の pushout から可算 nerve への単射性。 -/
lemma sequentialTelescopeInterval_injective_off_boundary {d : ℕ}
    (b c : (nerve (Discrete (ULift.{u} ℕ) × Fin 2)) _⦋d⦌)
    (hb : b ∉ Set.range
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app (Opposite.op ⦋d⦌)))
    (hc : c ∉ Set.range
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app (Opposite.op ⦋d⦌)))
    (he : (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u}).app _ b =
      (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u}).app _ c) : b = c := by
  have hb0 := sequentialTelescopeInterval_nonboundary_start b hb
  have hc0 := sequentialTelescopeInterval_nonboundary_start c hc
  have he0 := congrArg (fun s ↦ (s.obj 0).down) he
  change (b.obj 0).1.as.down + (b.obj 0).2.val =
    (c.obj 0).1.as.down + (c.obj 0).2.val at he0
  have hn : (b.obj 0).1.as = (c.obj 0).1.as := ULift.ext (by omega)
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦
    CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  have hni : (b.obj i).1.as = (c.obj i).1.as :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeInterval_index_eq b i).trans
      (hn.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeInterval_index_eq c i).symm)
  apply Prod.ext (Discrete.ext hni)
  apply Fin.ext
  have hei := congrArg (fun s ↦ (s.obj i).down) he
  change (b.obj i).1.as.down + (b.obj i).2.val =
    (c.obj i).1.as.down + (c.obj i).2.val at hei
  rw [hni] at hei
  omega

/-- 概要：離散端点・頂点・区間の正方形は可算 nerve 上で次数ごとに pullback。
方針：区間単体の像が定値なら区間成分も定値となることを使う。
規約：元の四つの nerve 写像を使う。
使われ方：pushout の比較射の単射性の判定。 -/
lemma sequentialTelescopeNerveSquare_isPullback (d : ℕ) :
    IsPullback
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u}).app (Opposite.op ⦋d⦌))
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app (Opposite.op ⦋d⦌))
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}).app (Opposite.op ⦋d⦌))
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u}).app (Opposite.op ⦋d⦌)) := by
  let nd := Opposite.op ⦋d⦌
  have hw : nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u} ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u} =
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u} ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u} := by
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u})
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeFunctor_condition]
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw nd, ?_, ?_⟩
  · intro a b hab
    have hm : Mono ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app nd) :=
      ((NatTrans.mono_iff_mono_app _).mp _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundary_mono) nd
    exact (mono_iff_injective _).mp hm hab.2
  · intro c b he
    have hconst (i : Fin (d + 1)) : (b.obj i).2 = (b.obj 0).2 := by
      have hc := Discrete.eq_of_hom (c.map (homOfLE (Fin.zero_le i)))
      have he0 := congrArg (fun s ↦ (s.obj 0).down) he
      have hei := congrArg (fun s ↦ (s.obj i).down) he
      change (c.obj 0).as.down = (b.obj 0).1.as.down + (b.obj 0).2.val at he0
      change (c.obj i).as.down = (b.obj i).1.as.down + (b.obj i).2.val at hei
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeInterval_index_eq b i, ← hc] at hei
      apply Fin.ext
      omega
    obtain ⟨a, ha⟩ := sequentialTelescopeInterval_mem_boundary b hconst
    refine ⟨a, ?_, ha⟩
    have hm : Mono ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}).app nd) :=
      ((NatTrans.mono_iff_mono_app _).mp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}
          (fun _ _ h ↦ Discrete.ext h))) nd
    apply (mono_iff_injective _).mp hm
    have hew := ConcreteCategory.congr_hom (NatTrans.congr_app hw nd) a
    change (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}).app nd
      ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u}).app nd a) =
      (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalFunctor.{u}).app nd
        ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}).app nd a) at hew
    rw [ha] at hew
    exact hew.trans he.symm

/-- 概要：望遠鏡から元の可算 nerve への写像は単射。
方針：次数ごとに端点の pullback と端点外の区間の単射性を既存の pushout 判定へ渡す。
規約：抽象的な同型な望遠鏡へ取り替えない。
使われ方：spine との strict な同型の単射部分。 -/
instance sequentialTelescopeToNerve_mono : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  let nd := Opposite.op ⦋d⦌
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj nd
  let f := nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u}
  let g := nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u}
  have hm : Mono ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}).app nd) :=
    ((NatTrans.mono_iff_mono_app _).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeVertexFunctor.{u}
        (fun _ _ h ↦ Discrete.ext h))) nd
  exact Types.mono_of_isPushout_of_isPullback
    ((IsPushout.of_hasPushout f g).map ev) (sequentialTelescopeNerveSquare_isPullback d)
    (NatTrans.congr_app _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve_vertices nd)
    (NatTrans.congr_app _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve_intervals nd)
    (sequentialTelescopeInterval_injective_off_boundary)

/-- 概要：望遠鏡から spine への写像は厳密な同型。
方針：可算 nerve への包含後の単射性と、区間族による spine の全射性を使う。
規約：次数ごとの全単体について全単射を確認する。
使われ方：spine の inner anodyne 比較を元の望遠鏡へ移す。 -/
instance sequentialTelescopeToSpine_isIso : IsIso _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine.{u} := by
  have hm : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine_ι]
    infer_instance
  have : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine.{u} := mono_of_mono _ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.ι
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨d⟩⟩
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).mp
    (((NatTrans.mono_iff_mono_app _).mp ‹Mono _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine.{u}›) _), ?_⟩
  intro s
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalToSpine_surjective.{u} d s
  let j := pushout.inr (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeAttachFunctor.{u})
    (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeBoundaryFunctor.{u})
  have hj : j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeIntervalToSpine.{u} :=
    pushout.inr_desc _ _ _
  exact ⟨j.app _ b, (ConcreteCategory.congr_hom (NatTrans.congr_app hj _) b).trans hb⟩

/-- 概要：元の望遠鏡から可算 nerve への写像は inner anodyne。
方針：spine との strict 同型と、その包含の inner anodyne 性を合成する。
規約：元の望遠鏡の写像を保持する。
使われ方：宇宙変更後にも同じ可算列の全余錐を比較する。 -/
lemma sequentialTelescopeToNerve_innerAnodyne :
    innerAnodyneExtensions _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve.{u} := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToSpine_ι, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.sequentialSpine_inclusion_innerAnodyne

/-- 概要：元の望遠鏡から可算 nerve への写像は、全関手の前合成同値を与える。
方針：spine との strict 同型と、その包含の inner anodyne 性を合成する。
規約：望遠鏡自体の quasicategory 性は要求しない。
使われ方：P-11 の元の可算列の全余錐の計算。 -/
lemma sequentialTelescopeToNerve_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialTelescopeToNerve.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne _ sequentialTelescopeToNerve_innerAnodyne

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
