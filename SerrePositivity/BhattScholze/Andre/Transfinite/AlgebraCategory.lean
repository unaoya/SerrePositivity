module

public import SerrePositivity.BhattScholze.Andre.Transfinite.AlgebraColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.CompletionUniversal
public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableRelations
public import SerrePositivity.BhattScholze.Andre.Transfinite.Terminal
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
/-- ## 概要
固定初段 R 上で perfectoid かつ p 完全忠実平坦な代数を、標準係数環射とともに束ねる。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環と係数環射をデータとして保持し、perfectoid 性と、その射の toAlgebra に関する完全忠実平坦性を記録する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
structure AndreTowerAlgebra where
  carrier : Type u
  [commRing : CommRing carrier]
  baseMap : R →+* carrier
  perfectoid : IsIntegralPerfectoid carrier p
  flat : letI := baseMap.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) carrier
attribute [instance] AndreTowerAlgebra.commRing
/-- ## 概要
塔の代数の台集合を同じ Type u の環として使う。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
構造の carrier 射影を CoeSort に用いる。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebraCoeSort : CoeSort (AndreTowerAlgebra R p) (Type u) :=
  ⟨AndreTowerAlgebra.carrier⟩
/-- ## 概要
塔の代数に元の標準係数環射による R 代数構造を与える。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
保持している baseMap の toAlgebra を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebraAlgebra (X : AndreTowerAlgebra R p) : Algebra R X := X.baseMap.toAlgebra
namespace AndreTowerAlgebra
variable {R p}
/-- ## 概要
固定初段上の塔の代数の射を、係数環射と両立する環準同型として定める。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環準同型とその係数射との合成が終域の係数射に等しいという条件を保持する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
structure Hom (X Y : AndreTowerAlgebra R p) where
  toRingHom : X →+* Y
  commutes : toRingHom.comp X.baseMap = Y.baseMap
/-- ## 概要
塔の代数の射は、その環準同型が等しければ等しい。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
構造を場合分けし、両立性条件の証明無関係性を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
@[ext]
theorem Hom.ext {X Y : AndreTowerAlgebra R p} {f g : Hom X Y}
    (h : f.toRingHom = g.toRingHom) : f = g := by cases f; cases g; congr
/-- ## 概要
固定初段上の perfectoid 完全忠実平坦代数と、通常の係数両立環射は圏をなす。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
恒等・合成は元の環準同型のものとし、係数との両立性は環射の結合律から示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance category : Category (AndreTowerAlgebra R p) where
  Hom := Hom
  id X := ⟨RingHom.id X, by ext x; rfl⟩
  comp f g := ⟨g.toRingHom.comp f.toRingHom, by rw [RingHom.comp_assoc, f.commutes, g.commutes]⟩
  id_comp := by intros; ext x; rfl
  comp_id := by intros; ext x; rfl
  assoc := by intros; ext x; rfl
/-- ## 概要
塔の代数は通常の p 進完備性を持つ。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
perfectoid の定義の完備性を取り出し、零環の場合は標準インスタンスを使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
theorem complete (X : AndreTowerAlgebra R p) : IsAdicComplete (Ideal.span {(p : X)}) X := by
  rcases X.perfectoid with hz | ⟨_, hc, _⟩
  · let := hz
    infer_instance
  · exact hc
variable {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (F : ι ⥤ AndreTowerAlgebra R p)
/-- ## 概要
塔の代数の図式から各段の同じ宇宙の環の台集合を取り出す。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の対象の carrier を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def diagramRing (i : ι) : Type u := F.obj i
/-- ## 概要
取り出した図式の各段に元の可換環構造を与える。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の束ねた環の構造をそのまま返す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramCommRing (i : ι) : CommRing (diagramRing F i) :=
  inferInstanceAs (CommRing (F.obj i))
/-- ## 概要
取り出した図式の各段に元の固定初段の係数作用を与える。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
各対象の baseMap から既に定めた代数構造をそのまま使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramAlgebra (i : ι) : Algebra R (diagramRing F i) :=
  inferInstanceAs (Algebra R (F.obj i))
/-- ## 概要
塔の代数の函手から、共通基底上の有向系の代数遷移射を取り出す。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の射の環準同型と係数射の両立条件を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def diagramMap (i j : ι) (h : i ≤ j) : diagramRing F i →ₐ[R] diagramRing F j :=
  { (F.map (homOfLE h)).toRingHom with
    commutes' := fun r ↦ RingHom.congr_fun (F.map (homOfLE h)).commutes r }
/-- ## 概要
函手から取り出した環と遷移射は DirectedSystem の恒等・合成条件を満たす。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の map_id と map_comp を元ごとの等式へ移す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramSystem : DirectedSystem (diagramRing F) (fun i j h ↦ diagramMap F i j h) where
  map_self := by
    intro i x
    change (F.map (𝟙 i)).toRingHom x = x
    rw [F.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    have he := F.map_comp (homOfLE hij) (homOfLE hjk)
    exact (congrArg (fun t ↦ t.toRingHom x) he).symm
local notation "S" => diagramRing F
local notation "maps" => diagramMap F
local notation "L" => Ring.DirectLimit S (fun i j h ↦ AlgHom.toRingHom (maps i j h))
local notation "C" => AdicCompletion (Ideal.span {(p : L)}) L
local notation "ofL" => Ring.DirectLimit.of S (fun i j h ↦ AlgHom.toRingHom (maps i j h))
/-- ## 概要
最小元を持つ有向添字の塔の代数の図式に対し、環余極限の通常 p 進完備化は再び塔の代数となる。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
Fontaine 表示による完備化の perfectoid 性と、各段の共通基底上の完全忠実平坦性を使う。
余極限の p 冪ねじれの境界 1 により、標準完備化射との合成も完全忠実平坦となる。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitObject : AndreTowerAlgebra R p := by
  let β := algebraRingDirectLimitBaseMap S maps
  let map : R →+* C := (algebraMap L C).comp β
  refine ⟨C, map, ?_, ?_⟩
  · exact isIntegralPerfectoid_adicCompletion_ringDirectLimit S
      (fun i j h ↦ AlgHom.toRingHom (maps i j h)) (fun i ↦ (F.obj i).perfectoid)
  · apply isCompletelyFaithfullyFlat_adicCompletion_comp p β
    · exact isCompletelyFaithfullyFlat_algebraRingDirectLimit S maps _ (fun i ↦ (F.obj i).flat)
    · refine ⟨1, ?_⟩
      intro n x hx
      simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid S
        (fun i j h ↦ AlgHom.toRingHom (maps i j h)) p (fun i ↦ (F.obj i).perfectoid) n x hx

/-- ## 概要
各段から完備化した余極限対象への標準射を、固定初段上の射として実現する。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の環余極限の標準段射を完備化射と合成し、基底写像の各段での表示で係数両立性を示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitOf (i : ι) : F.obj i ⟶ colimitObject F where
  toRingHom := (algebraMap L C).comp (ofL i)
  commutes := by
    ext r
    change algebraMap L C (ofL i ((F.obj i).baseMap r)) =
      algebraMap L C (algebraRingDirectLimitBaseMap S maps r)
    rw [algebraRingDirectLimitBaseMap_eq S maps i r]
    rfl

/-- ## 概要
完備化した余極限対象と標準段射は元の図式の余錐をなす。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環余極限の標準段射の両立性を完備化射で写す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitCocone : Cocone F where
  pt := colimitObject F
  ι :=
    { app := colimitOf F
      naturality := by
        intro i j h
        apply Hom.ext
        ext x
        change algebraMap L C (ofL j (maps i j (leOfHom h) x)) = algebraMap L C (ofL i x)
        exact congrArg (algebraMap L C) (Ring.DirectLimit.of_f
          (f := fun i j h ↦ AlgHom.toRingHom (maps i j h)) (leOfHom h) x) }

/-- ## 概要
任意の余錐に対し、完備化した余極限対象から余錐の頂点への標準射を構成する。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の環余極限の普遍代数射を作り、perfectoid な頂点の p 進完備性により延長する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitDesc (t : Cocone F) : colimitObject F ⟶ t.pt := by
  letI := algebraRingDirectLimitAlgebra S maps
  let α : ∀ i, S i →ₐ[R] t.pt := fun i ↦
    { (t.ι.app i).toRingHom with
      commutes' := fun r ↦ RingHom.congr_fun (t.ι.app i).commutes r }
  have hα : ∀ i j h x, α j (maps i j h x) = α i x := by
    intro i j h x
    exact congrArg (fun z ↦ z.toRingHom x) (t.w (homOfLE h))
  let q := algebraRingDirectLimitLift S maps α hα
  have hc := complete t.pt
  refine ⟨natAdicCompletionLift p q.toRingHom hc, ?_⟩
  ext r
  change natAdicCompletionLift p q.toRingHom hc
    (algebraMap L C (algebraRingDirectLimitBaseMap S maps r)) = t.pt.baseMap r
  rw [natAdicCompletionLift_of]
  exact q.commutes r

/-- ## 概要
余極限の標準普遍写像は各段射との合成で、与えられた余錐の射に一致する。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
通常完備化の標準延長と環余極限の持上げの計算規則を順に適用する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
theorem colimitDesc_fac (t : Cocone F) (i : ι) :
    colimitOf F i ≫ colimitDesc F t = t.ι.app i := by
  apply Hom.ext
  ext x
  change natAdicCompletionLift p _ (complete t.pt) (algebraMap L C (ofL i x)) = _
  rw [natAdicCompletionLift_of]
  exact algebraRingDirectLimitLift_of S maps _ _ i x

/-- ## 概要
構成した完備化余極限の余錐は、塔の代数の圏で実際の余極限である。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
標準普遍写像の因子分解を使い、一意性を完備化の環射の一意性と元の環余極限の一意性で示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac := colimitDesc_fac F
  uniq t m hm := by
    apply Hom.ext
    have hc : IsAdicComplete (Ideal.span {(p : t.pt)}) t.pt := by
      rcases t.pt.perfectoid with hz | ⟨_, hc, _⟩
      · let := hz
        infer_instance
      · exact hc
    apply natAdicCompletion_ringHom_ext p hc
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    exact congrArg (fun z ↦ z.toRingHom x) ((hm i).trans (colimitDesc_fac F t i).symm)

end AndreTowerAlgebra
/-- ## 概要
任意の非空整列線形順序 Type u による、塔の代数の圏の余極限が存在する。
BS Thm 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
整列順序の最小元を選び、完備化した環余極限と検証した普遍性を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebra_hasColimitsOfShape {ι : Type u}
    [LinearOrder ι] [Nonempty ι] [WellFoundedLT ι] :
    HasColimitsOfShape ι (AndreTowerAlgebra R p) := by
  let : OrderBot ι := WellFoundedLT.toOrderBot ι
  exact ⟨fun F ↦ ⟨⟨AndreTowerAlgebra.colimitCocone F, AndreTowerAlgebra.colimitIsColimit F⟩⟩⟩
end SerrePositivity.BhattScholze.Andre.Transfinite
