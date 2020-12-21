sig Float {}
// Geo location 
sig Position {
	latitude: one Float,
	longitude: one Float,
}

// time stamp which start from 1 jan 1970
sig DateTime {
	timestamp: one Int
} {
	timestamp >= 0
}

// define Super user
sig Username, Password, Certificate {}
abstract sig SuperUser {
	id: one Int,
	username: one Username,
	password: one Password
}{
	id >= 0 
}

// define Manager
sig Manager extends SuperUser {
	certificate: one Certificate,
} {
	id > 0 
}

// define User
sig User extends SuperUser {
	currentLocation: one Position,
	historyVisit: set UserVisitHistory,
	tickets: some Ticket
} {
	all t: tickets | t.qr.userId = id
}

// This is an anonymous user which get the ticket offline we choose id = 0 for them
sig OfflineUser extends User {} {
	id = 0
}

// define category
sig Category {
	capacity: one Int
} {
	capacity >= 0
}

// define the shop
sig Shop {
	id: one Int,
	manager: one Manager,
	capacity: one Int,
	categories: set Category,
	location: one Position,
	queue: one LineupQueue,
	start: one DateTime,
	end: one DateTime
} {
	id >0
	capacity >= 0
	start.timestamp < end.timestamp // shop can close shop after time it start it
}

// define User history
sig UserVisitHistory {
	start: one DateTime,
	end: one DateTime,
	categories: some Category
} {
	start.timestamp < end.timestamp // checkout time must be after user enter the shop
}

// define Ticket
// QR must encode the shopId and userId to a qrcode
sig QRCode {
	shopId: one Int,
	userId: one Int
}

// State of ticket for entrance
abstract sig State {}
sig Valid extends State{}
sig Invalid extends State{}

sig Ticket {
	qr: one QRCode,
	estimatedEntranceTime: one DateTime,
	state: one State
}

// define line up queue
sig LineupQueue {
	tickets: set Ticket,
	capacity: one Int
} {
	capacity >= #tickets // number of people are in the queue must be less than its capacity
}

// shops cannot have same queues
fact {
	no disj s1, s2: Shop | s1.queue = s2.queue
}

// define book a visit
sig BookAVisit {
	duration: lone Int,
	categories: some Category,
	selectedTime: one DateTime,
	ticket: one Ticket
}


///////////////////////////////////
/////// FACTS

// no same id and username for super users
fact {
	no disj p1, p2: SuperUser | p1.id = p2.id or p1.username = p2.username
}

// no same id for shop
fact {
	no disj s1, s2: Shop| s1.id = s2.id
}

// no same QR for each ticket
fact {
	no disj t1, t2: Ticket| t1.qr = t2.qr
}

// selected time must be available on that shop lineup
fact {
	all b: BookAVisit |  one s: Shop |
	 	b.ticket.qr.shopId = s.id and 
		b.selectedTime.timestamp >= s.start.timestamp and 
		b.selectedTime.timestamp < s.end.timestamp
}

// no same ticket for books
fact {
	no disj b1, b2: BookAVisit | b1.ticket = b2.ticket
}

// each ticket shop and user must exists
fact {
	all t: Ticket | one s: Shop | t.qr.shopId = s.id
	all t: Ticket | one u: User | t.qr.userId = u.id
}
///////////////////////////////////
/////// PREDICTIONS


// create shop
pred createShop(m: Manager, s: Shop, l: Position, st: DateTime, et: DateTime) {
	s.manager=m
	s.location = l
	s.start = st
	s.end =et
}

run createShop

// add to line up
pred addToLineup(u: User, s: Shop, t: Ticket) {
	t.state = Invalid
	t.qr.shopId = s.id
	t.qr.userId = u.id
	s.queue.tickets = s.queue.tickets + t
}

run addToLineup 

// book a Visit
pred bookVisit(u: User, s:Shop, t:Ticket, st: DateTime, b: BookAVisit) {
	t.state = Invalid
	t.qr.shopId = s.id
	t.qr.userId = u.id
	s.queue.tickets = s.queue.tickets + t
	b.ticket = t
	b.selectedTime = st
}

run bookVisit

// offline add to lineup
pred offlineLineup(u: OfflineUser,s: Shop, t: Ticket) {
	t.state = Invalid
	t.qr.shopId = s.id
	t.qr.userId = u.id
	s.queue.tickets = s.queue.tickets + t
}
	
run offlineLineup

// notify for entrance
pred notifyEntrance(u: User, t: Ticket) {
	t.qr.userId = u.id
	t.state = Invalid
}

run notifyEntrance

// enter the shop
pred allowEnter (u: User, s: Shop, t: Ticket, h: UserVisitHistory, n: DateTime){
	t.qr.userId = u.id
	t.qr.shopId = s.id
	t.state = Valid
	t in s.queue.tickets
	h.start = n
	u.historyVisit = u.historyVisit + h
}

run allowEnter

pred rejectEnter (u: User, s: Shop, t: Ticket){
	t.qr.userId = u.id
	t.qr.shopId = s.id
	t.state = Invalid or t not in s.queue.tickets
}

run rejectEnter

// checkout
pred checkout (u: User, s: Shop, t: Ticket, h: UserVisitHistory, n: DateTime, c: some Category){
	t.qr.userId = u.id
	t.qr.shopId = s.id
	t.state = Valid
	s.queue.tickets = s.queue.tickets - t
	h.end = n
	h in u.historyVisit
	h.categories = c
}

run checkout
