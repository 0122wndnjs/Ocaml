open Lwt

(* a list associating user nicknames to the output channels that write to their connections *)
(* Once we fix the other functions this should change to []*)
let sessions = ref []
(* Throwing the exception Quit *)
exception Quit
(* To use the Lwt_mutex.create(), I declared the mutex by making mut variable. *)
let mut = Lwt_mutex.create()

(* replace Lwt.return below with code that uses Lwt_list.iter_p to
  print sender: msg on each output channel (excluding the sender's)*)

(* This function is used when users write messages, when joining the chat or leaving the chat. I made it to print out the sender
when some other chat users send messages. So the form would be sender: message. To do that, I used Lwt_list.iter_p and made it
to show to every user except for sender. *)
let rec broadcast sender msg =  let test s =  match s with
  (name,output) -> if name <> sender then (Lwt_io.fprint output (sender^": ")
  >>= fun () -> Lwt_io.fprintl output msg) else Lwt.return ()
in Lwt_list.iter_p test !sessions

(* remove a session from the list of sessions: important so we don't try to write to a closed connection *)
let remove_session nn =
  sessions := List.remove_assoc nn !sessions;
  broadcast nn "<left chat>" >>= fun () ->
  Lwt.return ()

(* Modify to handle the "Quit" case separately, closing the channels before removing the session *)

(* This function is for handling the error. I declared the exception Quit above. And this function let the Quit to be handled. *)
let handle_error e nn inp outp = if e = Quit then Lwt_io.close inp >>=
fun () -> Lwt_io.close outp >>=
fun () -> remove_session nn else remove_session nn

(* modify sessions to remove (nn,outp) association, add (new_nn,outp) association.
   also notify other participants of new nickname *)

(* This function is changing the nickname. Whenever user use the /n to change the nick name, it will print out the new nickname.
When writer change the nickname, it will show to other users that the nickname was changed. The format of this is <changed nick to nn>
And after that, whenever the user who changed the nickname send the messages, the new nickname will be shown to the other users. *)
let change_nn nn outp new_nn = sessions := List.remove_assoc nn !sessions; sessions :=
(new_nn,outp)::!sessions; broadcast nn ("<changed nick to "^new_nn^">") >>=
fun () -> Lwt.return ()

(*  + obtain initial nick(name),
    + add (nick,outp) to !sessions, and
    + announce join to other users *)

(* This function is used in chat server. When server is connected, srvmain, which is the main function will call the
ChatServer.chat_handler with pair of inp, which is an input_channel and outp, which is an output_channel. First, I made it to
print out the message "Enter initial nick:" when the server is connected. I used Lwt_io.fprintl to print out this message.
Then, by using Lwt_io.read_line, it reads the user's nickname. After that, I used function to assign the new value to nick.
Also, I used Lwt_mutex.lock to lock the thread, and later used Lwt_mutex.unlock to unlock the thread. And I made another function
to update the sessions and it will include the new user and output pair. At last, I made a function to print out the <joined>
message when other uses joined the chat. So for example, if "JK" joined the chatroom, it will show as "JK: <joined>" to other users
except for JK itself. *)
let login_handler nr (inp,outp) = Lwt_io.fprintl outp "Enter initial nick:" >>=
  fun () -> Lwt_io.read_line inp >>=
  fun nick -> Lwt.return (nr := nick) >>=
  fun () -> Lwt_mutex.lock mut >>=
  fun () -> Lwt.return (sessions := (nick,outp)::!sessions) >>=
  fun () -> Lwt.return (Lwt_mutex.unlock mut ) >>=
  fun () -> broadcast !nr "<joined>"

(* modify handle_input below to detect /q, /n, and /l commands *)

(* Thie function is for handling the input. Whenver certain inputs are written, in this case, "/q", "/n", "/l", it will detect those
commands and do some actions. First of all, for "/q", which is the quit command, whenver it is written, it will quit the chat.
"/n" is the command for updating to the new nick name. So for example, if user writes "/n JK", the user's nickname will be updated
to JK. And because of change_nn, it will print "user: <changed nick to JK>" to all other users except for the user itself. Lastly,
"/l" is the command for listing the conneceted users. I used Lwt_list.iter_s to iterate over !sessions list and do actions for
(nickname,channel) pair. So whenever user writes /l on the chat, it will show all of the listings of connected chat users in the server.
For example, if there are 3 users. alice, bob and carol, shown in example. If any user write /l on the chat, it will print out
"alice bob carol" with spacing after each name. And for all these 3 cases, I used Str.string_before to show the previous string and
Str.string_after to show the updated status when needed. *)
let handle_input nr outp l =
  if (Str.string_before l 2) = "/q" then Lwt.fail Quit
  else if (Str.string_before l 2) = "/n" then change_nn !nr outp (Str.string_after l 3) >>=
  fun () -> Lwt.return (nr := (Str.string_after l 3))
  else if (Str.string_before l 2) = "/l" then let test str = match str with (nn,_) -> Lwt_io.fprintl outp nn in Lwt_list.iter_s test !sessions
  else broadcast !nr l

(* chat_handler is the main function with inp and outp pair. Before going through the main_loop, I called login_handler to make the
login_handler function to work. This is the only part that I modified and all other commands were already given and set up to work. *)
let chat_handler (inp,outp) =
  let nick = ref "" in
  (* replace () below with call to login_handler *)
  let _ = login_handler nick (inp,outp) in
  let rec main_loop () =
Lwt_io.read_line inp >>= handle_input nick outp >>= main_loop in
  Lwt.async (fun () -> Lwt.catch main_loop (fun e -> handle_error e !nick inp outp))
